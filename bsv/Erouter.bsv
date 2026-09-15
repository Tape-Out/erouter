package Erouter;

// IPv4 路由核：每口一块帧缓冲，存储转发。收完一帧、FCS 对了，才查链路层、查头部（RFC 1812 5.2.2）、
// 查 TTL、查路由表（最长前缀），然后把包挂到出口；出口边发边改写目的 MAC、源 MAC、TTL 与校验和，
// FCS 由 RmiiTx 重算。头部结构、校验和、表项匹配在 Ipv4（BH），挑表项在 hwcore 的 Match（BH）。
//
// 不做直通：RmiiTx 会给转出去的帧重算一个正确的 FCS，直通就把输入端的坏帧洗成了好帧。
// 同 eswitch：一条规则只调一次某个动作方法；入口、出口、计数各自一条规则，互相用线递消息。

import Vector::*;
import GetPut::*;
import RegFile::*;
import RegIf::*;
import RmiiTx::*;
import RmiiRx::*;
import Match::*;
import Ipv4::*;
import ErouterRegs::*;

typedef struct {
  Bit#(0) none;
} ErouterCfg;

interface ErouterPins#(numeric type ports);
  interface Vector#(ports, RmiiTxPins) tx;
  interface Vector#(ports, RmiiRxPins) rx;
endinterface

interface ErouterIfc#(numeric type aw, numeric type dw, numeric type ports, numeric type routes, numeric type mtu);
  interface RegIf#(aw, dw) regs;
  interface ErouterPins#(ports) pins;
endinterface

// 挂在出口上的一个包：去哪个口、下一跳的 MAC、帧长（不含 FCS）、改写后的 TTL 与校验和
typedef struct {
  UInt#(4)  out;
  Bit#(48)  nh;
  UInt#(11) flen;
  Bit#(8)   ttl;
  Bit#(16)  csum;
} Pending deriving (Bits);

// 一帧的去向，同时也是计数器的编号。构造子名避开 RmiiTx、RmiiRx 状态枚举里的 Idle、Fcs 等
typedef enum { Taken, Routed, BadFcs, NotMine, BadHdr, Expired, NoRoute, TooLong, Busy } Why deriving (Bits, Eq);

function RmiiTxPins getTxPins(RmiiTxIfc i) = i.pins;
function RmiiRxPins getRxPins(RmiiRxIfc i) = i.pins;

module mkErouter#(ErouterCfg cfg)(ErouterIfc#(aw, dw, ports, routes, mtu))
    provisos (Mul#(TDiv#(dw, 8), 8, dw), Add#(_a, 12, aw), Add#(_b, 1, dw), Add#(_c, 16, dw),
              Add#(_d, 32, dw), Add#(1, _e, routes), Add#(_f, TLog#(ports), 4));

  ErouterRegsIfc#(aw, dw, ports, routes) r <- mkErouterRegs;

  Vector#(ports, RmiiTxIfc) txp <- replicateM(mkRmiiTx);
  Vector#(ports, RmiiRxIfc) rxp <- replicateM(mkRmiiRx);

  Integer nport = valueOf(ports);
  Integer cap   = valueOf(mtu) + 4;   // 缓冲连 FCS 一起存，帧尾再去掉

  Vector#(ports, RegFile#(UInt#(11), Bit#(8))) buff <- replicateM(mkRegFile(0, fromInteger(cap - 1)));

  // ---- 每个入口的收帧状态 ----
  Vector#(ports, Reg#(UInt#(11)))   len     <- replicateM(mkReg(0));
  // 前 34 字节（以太网 14 + IPv4 20）按位置落格，不移位：不足 34 字节的帧移位会错开，
  // 本该判「IP 部分不足 20 字节」的帧就被当成目的 MAC 不对
  Vector#(ports, Vector#(34, Reg#(Bit#(8)))) hv <- replicateM(replicateM(mkReg(0)));
  Vector#(ports, Reg#(Bit#(16)))    sum     <- replicateM(mkReg(0));
  Vector#(ports, Reg#(Bit#(8)))     hiB     <- replicateM(mkReg(0));
  Vector#(ports, Reg#(Bit#(4)))     ihl     <- replicateM(mkReg(0));
  Vector#(ports, Reg#(Bool))        tooLong <- replicateM(mkReg(False));
  Vector#(ports, Reg#(Bool))        skip    <- replicateM(mkReg(False));  // 帧开头时口上还压着没发的包
  // 入口挂包、出口发完清掉：清的规则写 0 口，入口写 1 口
  Vector#(ports, Array#(Reg#(Maybe#(Pending)))) pend <- replicateM(mkCReg(2, tagged Invalid));

  // ---- 每个出口的发送状态 ----
  Vector#(ports, Reg#(Maybe#(UInt#(4)))) cur <- replicateM(mkReg(tagged Invalid));
  Vector#(ports, Reg#(UInt#(11)))        at  <- replicateM(mkReg(0));
  Vector#(ports, Reg#(UInt#(4)))         rr  <- replicateM(mkReg(0));

  // 出口 q 发完入口 p 的包：每对一根脉冲线，谁也不跟谁抢写
  Vector#(ports, Vector#(ports, PulseWire)) done <- replicateM(replicateM(mkPulseWire));
  Vector#(ports, RWire#(Why))               ev   <- replicateM(mkRWire);
  Vector#(9, Reg#(Bit#(32)))                cnt  <- replicateM(mkReg(0));

  function Bit#(48) macOf(Integer p) = {r.machi[p], r.maclo[p]};

  function Route routeAt(Integer i);
    Bit#(16) c = r.rcfg[i];
    return Route { prefix: r.rprefix[i], len: unpack(c[5:0]), port: unpack(c[11:8]),
                   nh: {r.rnhhi[i], r.rnhlo[i]}, valid: c[15] == 1 };
  endfunction
  Vector#(routes, Route) table_ = genWith(routeAt);

  function Maybe#(Pending) held(Array#(Reg#(Maybe#(Pending))) a) = a[0];

  for (Integer p = 0; p < nport; p = p + 1) begin
    rule ingress (r.ctrl_en == 1);
      let c <- rxp[p].rx.get;
      if (!c.last) begin
        Bool sk = len[p] == 0 ? isValid(pend[p][1]) : skip[p];
        if (len[p] == 0) skip[p] <= sk;
        if (!sk) begin
          if (len[p] < fromInteger(cap)) buff[p].upd(len[p], c.dat);
          else tooLong[p] <= True;
          if (len[p] < 34) hv[p][len[p]] <= c.dat;
          // IP 头部的反码和，边收边算（RFC 1071）；IHL 在 IP 部分第一个字节里
          if (len[p] >= 14) begin
            UInt#(11) i = len[p] - 14;
            Bit#(4) h = i == 0 ? c.dat[3:0] : ihl[p];
            UInt#(11) hl = unpack(zeroExtend(h)) * 4;
            if (i == 0) ihl[p] <= c.dat[3:0];
            if (i < hl) begin
              if (pack(i)[0] == 0) hiB[p] <= c.dat;
              else sum[p] <= onesAdd(sum[p], {hiB[p], c.dat});
            end
          end
        end
        if (len[p] != 2047) len[p] <= len[p] + 1;
      end else begin
        // 帧尾：去掉 4 字节 FCS 再判
        UInt#(11) flen = len[p] < 4 ? 0 : len[p] - 4;
        Bit#(272) hb   = pack(reverse(readVReg(hv[p])));
        Bit#(48)  dmac = hb[271:224];
        Bit#(16)  etyp = hb[175:160];
        Ipv4Hdr   ip   = unpack(hb[159:0]);
        Maybe#(UInt#(TLog#(routes))) hit = best(table_, ip.dst);
        Why why = Taken;
        Maybe#(Pending) np = tagged Invalid;
        if (skip[p]) why = Busy;
        else if (!c.fcsOk || len[p] < 4) why = BadFcs;
        else if (tooLong[p]) why = TooLong;
        else if (flen < 14 || etyp != 16'h0800 || dmac != macOf(p)) why = NotMine;
        else if (!headerOk(flen - 14, ip, sum[p])) why = BadHdr;
        // TTL 减一之后为 0 就丢（RFC 1812 5.3.1）；ICMP Time Exceeded 不发
        else if (ip.ttl <= 1) why = Expired;
        else if (hit matches tagged Valid .i &&& table_[i].port < fromInteger(nport)) begin
          Route rt = table_[i];
          Bit#(8) nt = ip.ttl - 1;
          // RFC 1624 Eqn. 3：变的只有 TTL 与 Protocol 那一个 16 位字
          np = tagged Valid Pending { out: rt.port, nh: rt.nh, flen: flen, ttl: nt,
                                      csum: ckUpdate(ip.csum, {ip.ttl, ip.proto}, {nt, ip.proto}) };
        end else why = NoRoute;
        if (isValid(np)) pend[p][1] <= np;
        ev[p].wset(why);
        len[p] <= 0; sum[p] <= 0; tooLong[p] <= False; skip[p] <= False;
      end
    endrule

    // 发完的包从入口上摘掉
    rule clear;
      Bool any = False;
      for (Integer q = 0; q < nport; q = q + 1) if (done[q][p]) any = True;
      if (any) pend[p][0] <= tagged Invalid;
    endrule
  end

  for (Integer q = 0; q < nport; q = q + 1) begin
    rule egress (r.ctrl_en == 1);
      Vector#(ports, Maybe#(Pending)) pv = map(held, pend);
      UInt#(11) k = at[q];
      Vector#(ports, Bit#(8)) bv = newVector;
      for (Integer i = 0; i < nport; i = i + 1) bv[i] = buff[i].sub(k);
      if (cur[q] matches tagged Valid .p) begin
        Pending t = fromMaybe(?, pv[p]);
        Vector#(6, Bit#(8)) nh  = unpack(t.nh);
        Vector#(6, Bit#(8)) own = unpack(macOf(q));
        Bit#(8) b = bv[p];
        Bit#(8) o = k < 6 ? nh[5 - k] : (k < 12 ? own[11 - k] : (k == 22 ? t.ttl :
                    (k == 24 ? t.csum[15:8] : (k == 25 ? t.csum[7:0] : b))));
        txp[q].tx.put(tuple2(o, k + 1 == t.flen));
        if (k + 1 == t.flen) begin
          cur[q] <= tagged Invalid;
          for (Integer i = 0; i < nport; i = i + 1) if (p == fromInteger(i)) done[q][i].send;
        end else at[q] <= k + 1;
      end else begin
        // 轮转挑一个挂到本口的入口
        Maybe#(UInt#(4)) pick = tagged Invalid;
        for (Integer i = 0; i < nport; i = i + 1) begin
          UInt#(5) w = zeroExtend(rr[q]) + fromInteger(i);
          if (w >= fromInteger(nport)) w = w - fromInteger(nport);
          UInt#(4) p = truncate(w);
          if (!isValid(pick) &&& pv[p] matches tagged Valid .t &&& t.out == fromInteger(q))
            pick = tagged Valid p;
        end
        if (pick matches tagged Valid .p) begin
          cur[q] <= pick; at[q] <= 0;
          rr[q] <= p + 1 == fromInteger(nport) ? 0 : p + 1;
        end
      end
    endrule
  end

  // 计数：同一拍几个口各报一件事，按去向加起来。局部向量只能按编译期下标改，所以外层按去向展开、
  // 里层数有几个口报了它（按运行时的去向去改 add[pack(w)]，bsc 求不出下标，G0013）
  rule count;
    for (Integer i = 0; i < 9; i = i + 1) begin
      UInt#(4) n = 0;
      for (Integer p = 0; p < nport; p = p + 1) begin
        if (ev[p].wget matches tagged Valid .w &&& (i == 0 || pack(w) == fromInteger(i))) n = n + 1;
        if (i == 1) for (Integer q = 0; q < nport; q = q + 1) if (done[q][p]) n = n + 1;
      end
      cnt[i] <= cnt[i] + zeroExtend(pack(n));
    end
  endrule

  rule publish;
    r.rxcnt_in(cnt[pack(Taken)]);
    r.fwdcnt_in(cnt[pack(Routed)]);
    r.fcscnt_in(cnt[pack(BadFcs)]);
    r.l2cnt_in(cnt[pack(NotMine)]);
    r.hdrcnt_in(cnt[pack(BadHdr)]);
    r.ttlcnt_in(cnt[pack(Expired)]);
    r.routecnt_in(cnt[pack(NoRoute)]);
    r.longcnt_in(cnt[pack(TooLong)]);
    r.busycnt_in(cnt[pack(Busy)]);
  endrule

  interface regs = r.regs;
  interface ErouterPins pins;
    interface tx = map(getTxPins, txp);
    interface rx = map(getRxPins, rxp);
  endinterface
endmodule

endpackage
