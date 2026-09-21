"""erouter 的行为测试台：包从哪个口出、出来的每个字节对不对、丢掉的包记在哪个计数器上。

每口一个 `mkRmiiTx` 当激励、一个 `mkRmiiRx` 当监视，都是 emac 环回测过的现成件。
期望输出由本脚本从头算：目的 MAC 换成下一跳、源 MAC 换成出口地址、TTL 减一、校验和**整体重算**，
与被测件的 RFC 1624 增量更新是两条独立的算法。监视器不逐字节比，而是比「长度 + FCS」：
出口的 FCS 是被测件的 RmiiTx 对它实际发出的字节算的，任何一个字节错了 CRC-32 都对不上。
同一口上的包不论先后（第 7 条两口同时发），先后由每一段结束时各口的收包数钉住。

测试台是一段小程序加一个解释器：每一步一拍（写寄存器、读计数器比对、起一帧、等），
避开 StmtFSM 的展开步数上限；报错文字按步号挑，指得出是哪一条判据。

认矩阵：`ports`、`routes`、`mtu` 从这一点的旋钮来。口数少于 4 时出口按口数取模，
路由表只有两项时缺省路由暂占第二项、测完写回。
"""
import json
import pathlib
import sys
import zlib

out = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else ".")
out.mkdir(parents=True, exist_ok=True)
cfg = json.loads(sys.argv[2]) if len(sys.argv) > 2 else {}
label = cfg.get("label", "")
k = cfg.get("knobs", {})
P = int(k.get("ports", 4))
R = int(k.get("routes", 8))
M = int(k.get("mtu", 256))

H = 40          # 帧的前 H 字节查表，之后的字节按 pat 公式，长帧不必整帧进表
HOST = [0x02, 0x11, 0x22, 0x33, 0x44, 0x55]
NH = {"A": [0x02, 0xAA, 0x00, 0x00, 0x00, 0x0A],
      "B": [0x02, 0xAA, 0x00, 0x00, 0x00, 0x0B],
      "C": [0x02, 0xAA, 0x00, 0x00, 0x00, 0x0C]}
OA, OB, OC = 1, 2 % P, 3 % P
LAST = P - 1
IA, IB = 0, R - 1
IC = 1 if R >= 3 else R - 1


def mac(p):
    return [0x02, 0x52, 0x54, 0x00, 0x10, p]


def ip4(a, b, c, d):
    return (a << 24) | (b << 16) | (c << 8) | d


def pat(f, i):
    return (i * 7 + f * 13) & 0xFF


def onesadd(a, b):
    s = a + b
    return (s & 0xFFFF) + (s >> 16)


def ones(bs):
    s = 0
    for i in range(0, len(bs) - 1, 2):
        s = onesadd(s, (bs[i] << 8) | bs[i + 1])
    return s


FR = []


def iphdr(dst, n, ttl, ident, ver, ihl, total):
    tot = (n - 14) if total is None else total
    return [(ver << 4) | ihl, 0, tot >> 8, tot & 0xFF, ident >> 8, ident & 0xFF, 0x40, 0x00,
            ttl, 17, 0, 0, 192, 168, 0, 9,
            dst >> 24, (dst >> 16) & 0xFF, (dst >> 8) & 0xFF, dst & 0xFF]


def frame(dst, *, port=0, n=64, ttl=64, ident=0x1C46, ver=4, ihl=5, total=None, opts=(),
          etype=0x0800, dmac=None, ckflip=0):
    f = len(FR)
    ipb = iphdr(dst, n, ttl, ident, ver, ihl, total) + list(opts)
    full = max(n, 14 + 4 * max(ihl, 5), 14 + len(ipb))
    b = [pat(f, i) for i in range(full)]
    b[0:6] = mac(port) if dmac is None else dmac
    b[6:12] = HOST
    b[12:14] = [etype >> 8, etype & 0xFF]
    b[14:14 + len(ipb)] = ipb
    cover = min(4 * ihl, n - 14)

    # 校验和只盖被测件真会加的那些字节（IHL×4 与实到字节数取小），于是 IHL 4、IHL 15 这类包的
    # 校验和是对的，拦下它们的只能是各自那一项检查，不会先被校验和那一项顺手拦掉
    def seal():
        b[24:26] = [0, 0]
        ck = (~ones(b[14:14 + cover])) & 0xFFFF ^ ckflip
        b[24:26] = [ck >> 8, ck & 0xFF]

    seal()
    # 头部声称比帧长时，被测件边收边加、不知道帧在哪儿结束，4 个 FCS 字节也进了反码和，校验和那一项
    # 又先拦下了（变异 m14 第二次还是绿的原因）。挑两个载荷字节，让 FCS 的两个 16 位字在反码加里
    # 恰好抵消：这样的帧真能过校验和，拦下它的只剩「头部装不下」
    # 命中率每次约 1/65536：两个字节只有 65536 种取值，一次都不中的机会约三分之一（第一版就没中），取三个字节
    if ver == 4 and ihl >= 5 and 4 * ihl > n - 14 >= 20 and (n - 14) % 2 == 0:
        for t in range(1 << 24):
            b[36:39] = [t >> 16, (t >> 8) & 0xFF, t & 0xFF]
            seal()
            fcs = zlib.crc32(bytes(b[:n])).to_bytes(4, "little")
            if onesadd(onesadd(0xFFFF, (fcs[0] << 8) | fcs[1]), (fcs[2] << 8) | fcs[3]) == 0xFFFF:
                break
        else:
            raise SystemExit("找不到让 FCS 两个字抵消的载荷字节")
    assert 14 + len(ipb) <= H
    FR.append(b[:n])
    return f


def forwarded(f, o, nh):
    b = list(FR[f])
    b[0:6] = NH[nh]
    b[6:12] = mac(o)
    b[22] -= 1
    b[24:26] = [0, 0]
    ihl = b[14] & 0xF
    ck = (~ones(b[14:14 + 4 * ihl])) & 0xFFFF
    b[24:26] = [ck >> 8, ck & 0xFF]
    return b


def sig(b):
    return len(b) + 4, int.from_bytes(zlib.crc32(bytes(b)).to_bytes(4, "little"), "big")


COUNTERS = ["rxcnt", "fwdcnt", "fcscnt", "l2cnt", "hdrcnt", "ttlcnt", "routecnt", "longcnt", "busycnt"]
ADDR = {c: 0x400 + 4 * i for i, c in enumerate(COUNTERS)}
CNT = {c: 0 for c in COUNTERS}
EXP = [[] for _ in range(P)]
OPS = []        # (op, a, v, 报错文字)
case = ""


def W(a, v):
    OPS.append((1, a, v, None))


def C(a, v, msg):
    OPS.append((2, a, v, msg))


def S(port, f, bad=False):
    OPS.append((3, port, f | (0x10000 if bad else 0), None))


def Q():
    OPS.append((4, 0, 0, None))


def D(n):
    OPS.append((5, 0, n, None))


def settle(*fs):
    Q()
    D(8 * (max(len(FR[f]) for f in fs) + 12) + 400)


def fwd(port, f, o, nh):
    S(port, f)
    settle(f)
    CNT["rxcnt"] += 1
    CNT["fwdcnt"] += 1
    EXP[o].append(sig(forwarded(f, o, nh)))


def drop(port, f, why, bad=False):
    S(port, f, bad)
    settle(f)
    CNT["rxcnt"] += 1
    CNT[why] += 1


def check():
    for c in COUNTERS:
        C(ADDR[c], CNT[c], f"{case}: {c} is %0d, want %0d")
    v = 0
    for q in range(P):
        v |= len(EXP[q]) << (8 * q)
    OPS.append((6, 0, v, f"{case}: port %0d had sent %0d frames, want %0d"))


def route(i, pfx, ln, o, nh):
    m = NH[nh]
    W(0x100 + 16 * i, pfx)
    W(0x104 + 16 * i, 0x8000 | (o << 8) | ln)
    W(0x108 + 16 * i, (m[0] << 8) | m[1])
    W(0x10C + 16 * i, (m[2] << 24) | (m[3] << 16) | (m[4] << 8) | m[5])


# ---- 装表 ----
W(0x000, 1)
for p in range(P):
    W(0x010 + 8 * p, (mac(p)[0] << 8) | mac(p)[1])
    W(0x014 + 8 * p, (mac(p)[2] << 24) | (mac(p)[3] << 16) | (mac(p)[4] << 8) | mac(p)[5])
# /8 在表头、/16 在表尾：取第一个命中的写法会挑中 /8
route(IA, ip4(10, 0, 0, 0), 8, OA, "A")
route(IB, ip4(10, 1, 0, 0), 16, OB, "B")
D(10)

# 1：最长前缀。10.0.0.1 与 10.1.128.9 各卡掩码边界的一侧：掩码少一位或多一位都会走错口
case = "longest prefix"
fwd(0, frame(ip4(10, 1, 2, 3)), OB, "B")
fwd(0, frame(ip4(10, 2, 0, 1)), OA, "A")
fwd(0, frame(ip4(10, 0, 0, 1)), OA, "A")
fwd(0, frame(ip4(10, 1, 128, 9)), OB, "B")
check()

# 2：没有命中就丢；写一条缺省路由之后同一个目的地址从缺省口出，而更长的前缀仍然赢
case = "default route"
drop(0, frame(ip4(11, 0, 0, 1)), "routecnt")
# 命中的表项指向不存在的口：当无路由丢，不能挂到一个永远没人发的出口上把入口堵死
route(IC, ip4(11, 0, 0, 0), 8, 15, "C")
D(10)
drop(0, frame(ip4(11, 0, 0, 1)), "routecnt")
route(IC, 0, 0, OC, "C")
D(10)
fwd(0, frame(ip4(11, 0, 0, 1)), OC, "C")
if R >= 3:
    fwd(0, frame(ip4(10, 1, 2, 3)), OB, "B")
else:
    route(IB, ip4(10, 1, 0, 0), 16, OB, "B")
    D(10)
check()

# 一样长的两条都命中取表里靠前的一项（笔记第 7 行自定）。要两个空表项，表有五项以上才测
if R >= 5:
    case = "equal length"
    route(2, ip4(10, 2, 0, 0), 16, OC, "C")
    route(3, ip4(10, 2, 0, 0), 16, OA, "A")
    D(10)
    fwd(0, frame(ip4(10, 2, 0, 1)), OC, "C")
    W(0x104 + 16 * 2, 0)
    W(0x104 + 16 * 3, 0)
    D(10)
    check()

# 3：TTL（RFC 1812 5.3.1）
case = "TTL"
drop(0, frame(ip4(10, 2, 0, 1), ttl=1), "ttlcnt")
drop(0, frame(ip4(10, 2, 0, 1), ttl=0), "ttlcnt")
fwd(0, frame(ip4(10, 2, 0, 1), ttl=2), OA, "A")
check()

# 4：RFC 1812 5.2.2 的五项，另加头部装不下
case = "header checks"
drop(0, frame(ip4(10, 2, 0, 1), ckflip=0x0100), "hdrcnt")
drop(0, frame(ip4(10, 2, 0, 1), ver=6), "hdrcnt")
drop(0, frame(ip4(10, 2, 0, 1), ihl=4), "hdrcnt")
drop(0, frame(ip4(10, 2, 0, 1), total=19), "hdrcnt")
drop(0, frame(ip4(10, 2, 0, 1), n=33), "hdrcnt")
# IHL 15 而 IP 部分只有 50 字节。Total Length 写 60：写成实到的 50 会先被「Total Length 不小于 IHL×4」
# 那一项拦下，「头部装不下」这一项就没有只有它拦得住的用例（变异 m14 第一次跑因此是绿的）
drop(0, frame(ip4(10, 2, 0, 1), ihl=15, total=60), "hdrcnt")
check()

# 5：带 4 字节选项（Router Alert）的包原样转出，校验和盖住 24 字节
case = "options"
fwd(0, frame(ip4(10, 2, 0, 1), ihl=6, opts=(0x94, 0x04, 0x00, 0x00)), OA, "A")
check()

# 6：链路层：坏 FCS、ARP、别的口的 MAC、广播
case = "link layer"
drop(0, frame(ip4(10, 2, 0, 1)), "fcscnt", bad=True)
drop(0, frame(ip4(10, 2, 0, 1), etype=0x0806), "l2cnt")
drop(0, frame(ip4(10, 2, 0, 1), dmac=mac(1 % P) if P > 1 else [0x02] * 6), "l2cnt")
drop(0, frame(ip4(10, 2, 0, 1), dmac=[0xFF] * 6), "l2cnt")
check()

# 7：两个口同时往同一个出口送
case = "contention"
fa = frame(ip4(10, 1, 2, 3), port=0)
fb = frame(ip4(10, 1, 7, 7), port=LAST)
S(0, fa)
S(LAST, fb)
Q()
D(16 * 76 + 800)
CNT["rxcnt"] += 2
CNT["fwdcnt"] += 2
EXP[OB].append(sig(forwarded(fa, OB, "B")))
EXP[OB].append(sig(forwarded(fb, OB, "B")))
check()

# 8：校验和的 −0。挑 Identification 让转发后整体重算的校验和恰为 0x0000
case = "checksum -0"
s0 = ones(iphdr(ip4(10, 2, 0, 1), 64, 63, 0, 4, 5, None))
ident = (0xFFFF - s0) & 0xFFFF
assert onesadd(s0, ident) == 0xFFFF
fz = frame(ip4(10, 2, 0, 1), ttl=64, ident=ident)
want = forwarded(fz, OA, "A")
assert want[24:26] == [0, 0], want[24:26]
hc = (FR[fz][24] << 8) | FR[fz][25]
eqn2 = onesadd(onesadd(hc, (64 << 8) | 17), (~((63 << 8) | 17)) & 0xFFFF)
assert eqn2 == 0xFFFF, hex(eqn2)
fwd(0, fz, OA, "A")
check()

# 9：帧缓冲的边界：恰好 mtu 字节的转出，多一个字节的丢
case = "frame buffer"
drop(0, frame(ip4(10, 2, 0, 1), n=M + 1), "longcnt")
fwd(0, frame(ip4(10, 2, 0, 1), n=M), OA, "A")
check()

# 10：入口一次只存一帧：前一个包还没发完时背靠背来的第二帧丢弃计数
case = "busy port"
f1 = frame(ip4(10, 2, 0, 1))
f2 = frame(ip4(10, 2, 0, 2))
S(0, f1)
Q()
S(0, f2)
settle(f1)
CNT["rxcnt"] += 2
CNT["fwdcnt"] += 1
CNT["busycnt"] += 1
EXP[OA].append(sig(forwarded(f1, OA, "A")))
check()

OPS.append((7, 0, 0, None))

assert len(OPS) < 1024 and len(FR) < 256
assert all(len(e) < 32 for e in EXP)
LIMIT = sum(v for op, _, v, _ in OPS if op == 5) + sum(4 * (len(b) + 20) for b in FR) + 30000

progrows = "\n".join(f"    {i}: return Op {{ op: {op}, a: 12'h{a:03X}, v: 32'h{v:08X} }};"
                     for i, (op, a, v, _) in enumerate(OPS))
sayc = "\n".join(f'      {i}: $display("FAIL {msg}", got, want);'
                 for i, (op, _, _, msg) in enumerate(OPS) if op == 2)
sayk = "\n".join(f'      {i}: $display("FAIL {msg}", q, got, want);'
                 for i, (op, _, _, msg) in enumerate(OPS) if op == 6)
romrows = "\n".join(f"    14'h{(f << 6) | i:04X}: x = 8'h{b[i]:02X};"
                    for f, b in enumerate(FR) for i in range(min(H, len(b))))
lenrows = "\n".join(f"    {f}: return {len(b)};" for f, b in enumerate(FR))


def monitor(q):
    arms = "\n".join(
        f"      if (!hit && sn[{j}] == 0 && n == {ln} && s == 32'h{fcs:08X}) begin sn[{j}] = 1; hit = True; end"
        for j, (ln, fcs) in enumerate(EXP[q]))
    return f"""
  rule mon{q};
    let c <- mon[{q}].rx.get;
    if (!c.last) begin
      mN[{q}] <= mN[{q}] + 1;
      mL[{q}] <= {{mL[{q}][23:0], c.dat}};
    end else begin
      UInt#(11) n = mN[{q}];
      Bit#(32) s = mL[{q}];
      Bit#(32) sn = seen[{q}];
      Bool hit = False;
{arms}
      seen[{q}] <= sn;
      mN[{q}] <= 0;
      nrecv[{q}] <= nrecv[{q}] + 1;
      if (!c.fcsOk) begin
        $display("FAIL port {q} sent a frame with a bad FCS");
        badM[{q}] <= True;
      end else if (!hit) begin
        $display("FAIL port {q} sent a frame nobody expected: %0d bytes with FCS, FCS %08h", n, s);
        badM[{q}] <= True;
      end
    end
  endrule"""


monitors = "".join(monitor(q) for q in range(P))

txt = f'''package Erouter{label}Tb;

import Vector::*;
import ConfigReg::*;
import RegIf::*;
import GetPut::*;
import RmiiTx::*;
import RmiiRx::*;
import Erouter::*;

// 由 tb/mkeroutertb.py 生成，勿手改。
// 这一点：ports={P} routes={R} mtu={M}

typedef struct {{
  Bit#(3)  op;
  Bit#(12) a;
  Bit#(32) v;
}} Op deriving (Bits);

function Op prog(UInt#(10) pc);
  case (pc)
{progrows}
    default: return Op {{ op: 7, a: 0, v: 0 }};
  endcase
endfunction

function Bit#(8) fbyte(UInt#(8) f, UInt#(11) i);
  Bit#(16) y = zeroExtend(pack(i)) * 7 + zeroExtend(pack(f)) * 13;
  Bit#(8) x = y[7:0];
  if (i < {H})
    case ({{pack(f), pack(i)[5:0]}})
{romrows}
    endcase
  return x;
endfunction

function UInt#(11) flenOf(UInt#(8) f);
  case (f)
{lenrows}
    default: return 1;
  endcase
endfunction

function Action sayC(UInt#(10) pc, Bit#(32) got, Bit#(32) want);
  action
    case (pc)
{sayc}
      default: $display("FAIL step %0d read %0d, want %0d", pc, got, want);
    endcase
  endaction
endfunction

function Action sayK(UInt#(10) pc, Integer q, Bit#(8) got, Bit#(8) want);
  action
    case (pc)
{sayk}
      default: $display("FAIL step %0d port %0d had sent %0d frames, want %0d", pc, q, got, want);
    endcase
  endaction
endfunction

(* synthesize *)
module mkErouter{label}Tb(Empty);
  ErouterIfc#(12, 32, {P}, {R}, {M}) d <- mkErouter(ErouterCfg {{ none: 0 }});
  Vector#({P}, RmiiTxIfc) gen <- replicateM(mkRmiiTx);
  Vector#({P}, RmiiRxIfc) mon <- replicateM(mkRmiiRx);

  Reg#(UInt#(10)) pc  <- mkReg(0);
  Reg#(Bit#(32))  w   <- mkReg(0);
  Reg#(Bool)      badS <- mkReg(False);
  // 各规则之间互相读的状态用 ConfigReg：普通寄存器会让读写顺序绕成环，把规则整条挡掉
  Reg#(Bit#(32))  cyc <- mkConfigReg(0);

  // 激励：解释器在 1 口置忙，发送规则发完在 0 口清
  Vector#({P}, Array#(Reg#(Bool))) fBusy <- replicateM(mkCReg(2, False));
  Vector#({P}, Reg#(UInt#(8)))  fFrame <- replicateM(mkConfigReg(0));
  Vector#({P}, Reg#(UInt#(11))) fAt    <- replicateM(mkReg(0));
  Vector#({P}, Reg#(Bool))      badArm <- replicateM(mkConfigReg(False));
  Vector#({P}, Reg#(UInt#(16))) ic     <- replicateM(mkReg(0));

  // 监视
  Vector#({P}, Reg#(UInt#(11))) mN    <- replicateM(mkReg(0));
  Vector#({P}, Reg#(Bit#(32)))  mL    <- replicateM(mkReg(0));
  Vector#({P}, Reg#(Bit#(32)))  seen  <- replicateM(mkReg(0));
  Vector#({P}, Reg#(Bit#(8)))   nrecv <- replicateM(mkConfigReg(0));
  Vector#({P}, Reg#(Bool))      badM  <- replicateM(mkConfigReg(False));

  rule tick_;
    cyc <= cyc + 1;
    if (cyc > {LIMIT}) begin
      $display("TIMEOUT at step %0d", pc);
      $finish(1);
    end
  endrule

  // 激励源接到被测件的入口；要造坏 FCS 时在帧里第 200 拍翻一位（落在 IP 头部之后）
  rule wires;
    for (Integer p = 0; p < {P}; p = p + 1) begin
      Bool en = gen[p].pins.tx_en;
      Bit#(2) dd = gen[p].pins.txd;
      if (en && badArm[p] && ic[p] == 200) dd = dd ^ 2'b01;
      d.pins.rx[p].wire_in(dd, en, False);
      ic[p] <= en ? ic[p] + 1 : 0;
      mon[p].pins.wire_in(d.pins.tx[p].txd, d.pins.tx[p].tx_en, False);
    end
  endrule

  for (Integer p = 0; p < {P}; p = p + 1) begin
    rule feed (fBusy[p][0]);
      UInt#(8) f = fFrame[p];
      UInt#(11) i = fAt[p];
      Bool lst = i + 1 == flenOf(f);
      gen[p].tx.put(tuple2(fbyte(f, i), lst));
      if (lst) begin
        fBusy[p][0] <= False;
        fAt[p] <= 0;
      end else fAt[p] <= i + 1;
    endrule
  end
{monitors}

  rule step;
    Op o = prog(pc);
    case (o.op)
      1, 2: begin
        let x <- d.regs.access(RegReq {{ addr: o.a, write: o.op == 1, wdata: o.v, wstrb: 4'hF }});
        if (o.op == 2 && x.rdata != o.v) begin
          sayC(pc, x.rdata, o.v);
          badS <= True;
        end
        pc <= pc + 1;
      end
      3: begin
        for (Integer p = 0; p < {P}; p = p + 1)
          if (o.a == fromInteger(p)) begin
            fFrame[p] <= unpack(o.v[7:0]);
            badArm[p] <= o.v[16] == 1;
            fBusy[p][1] <= True;
          end
        pc <= pc + 1;
      end
      4: begin
        Bool idle = True;
        for (Integer p = 0; p < {P}; p = p + 1) if (fBusy[p][1]) idle = False;
        if (idle) pc <= pc + 1;
      end
      5: begin
        if (w + 1 >= o.v) begin
          w <= 0;
          pc <= pc + 1;
        end else w <= w + 1;
      end
      6: begin
        Bool kb = False;
        for (Integer q = 0; q < {P}; q = q + 1) begin
          Bit#(8) want = o.v[8 * q + 7:8 * q];
          if (nrecv[q] != want) begin
            sayK(pc, q, nrecv[q], want);
            kb = True;
          end
        end
        if (kb) badS <= True;
        pc <= pc + 1;
      end
      default: begin
        Bool bad = badS;
        for (Integer q = 0; q < {P}; q = q + 1) if (badM[q]) bad = True;
        if (bad) $display("FAILED");
        else $display("PASS erouter: the longest matching prefix picks the port, RFC 1812 header and TTL checks drop what they must, the incremental checksum matches a full recompute including -0, and every drop is counted by reason");
        $finish(bad ? 1 : 0);
      end
    endcase
  endrule
endmodule

endpackage
'''

(out / f"Erouter{label}Tb.bsv").write_text(txt, encoding="utf-8")
print(f"  erouter 行为测试台就位：ports={P} routes={R} mtu={M}，{len(OPS)} 步、{len(FR)} 帧")
