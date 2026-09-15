# erouter

IPv4 router over RMII Ethernet ports.

![maturity](https://img.shields.io/badge/maturity-simulated-yellow) ![license](https://img.shields.io/badge/license-MulanPSL--2.0-blue)

Part of the [Tape-Out](https://github.com/Tape-Out) IP library: Bluespec IP over the
bus-neutral contracts in [`hwcore`](https://github.com/Tape-Out/hwcore), assembled by
[`xirang`](https://github.com/Tape-Out/xirang). Maturity runs `planned` -> `simulated` ->
`fpga-proven` -> `asic-ready` -> `silicon-proven`.

## Status

Simulated. The IP forwards IPv4 packets between `ports` RMII interfaces, using the receiver and transmitter from [`emac`](https://github.com/Tape-Out/emac).

It is store-and-forward: each input keeps one frame in a buffer of `mtu` bytes and decides only when the whole frame is in and its FCS is good. A cut-through router would rewrite the header of a frame whose FCS it has not seen yet, and the output transmitter would then give that bad frame a new, valid FCS.

A frame is accepted when its destination MAC is the input port's address and its EtherType is 0x0800. The header then goes through the five checks of RFC 1812 section 5.2.2, which cannot be switched off, plus a check that the header fits in the frame. A packet whose TTL is 0 or 1 is dropped; otherwise the TTL is decremented and the header checksum updated with RFC 1624 equation 3. The route table is searched for the longest matching prefix (RFC 1812 section 5.2.4.3); on a tie the lower entry wins. The output port rewrites the destination MAC to the route's next hop and the source MAC to its own address. Every dropped frame is counted by reason.

`hwcore/Match.bs` holds the table search in Bluespec Haskell: a `Match` class with two instances, exact keys for `Cam` and prefixes for routes, and one balanced-tree `best` that picks the matching entry of highest rank. `Ipv4.bs` holds the header layout, the one's complement sum, the incremental update and the header checks; at compile time it checks the update against the example in RFC 1624 section 4, and the build stops if they disagree. `Erouter.bsv` is the per-port receive, decide and transmit engine.

The testbench drives every port with an `RmiiTx` and watches every port with an `RmiiRx`. It builds each frame in Python and computes the expected output independently, recomputing the whole checksum rather than updating it. Output frames are compared by length and FCS, which the device's own transmitter computes over the bytes it actually sent. It checks:

- the longest prefix winning over a shorter one earlier in the table, and addresses one bit either side of a prefix boundary;
- a dropped packet with no route, a matching route to a port that does not exist also dropped, then the same packet leaving through a default route;
- two equally long prefixes, where the lower table entry wins;
- TTL 0 and 1 dropped, TTL 2 forwarded as 1;
- a wrong checksum, version 6, IHL 4, a total length below the header length, fewer than 20 bytes of IP, and an IHL longer than the frame, each dropped and counted. Each of these packets is built so that only its own check can drop it: the checksum covers exactly the bytes the router sums, and for the header longer than the frame, whose FCS bytes the router cannot tell from header bytes, the payload is chosen so the two FCS words cancel in the one's complement sum;
- a header with options forwarded unchanged apart from TTL and checksum;
- a bad FCS, an ARP frame, another port's MAC and a broadcast, each dropped and counted;
- two ports sending to the same output at once;
- a packet whose updated checksum must be 0x0000, which equation 2 of RFC 1624 would give as 0xFFFF;
- a frame of exactly `mtu` bytes forwarded and one byte more dropped;
- a frame arriving while its port still holds an unsent packet, dropped and counted.

## Registers

| Offset | Register | Contents |
| :--: | :--: | :-- |
| 0x000 | `ctrl` | `en` |
| 0x010 + 8·p | `machi[p]` | MAC address of port p, high 16 bits |
| 0x014 + 8·p | `maclo[p]` | MAC address of port p, low 32 bits |
| 0x100 + 16·i | `rprefix[i]` | route destination prefix |
| 0x104 + 16·i | `rcfg[i]` | prefix length (5:0), output port (11:8), valid (15) |
| 0x108 + 16·i | `rnhhi[i]` | next hop MAC, high 16 bits |
| 0x10C + 16·i | `rnhlo[i]` | next hop MAC, low 32 bits |
| 0x400 | `rxcnt` | frames received |
| 0x404 | `fwdcnt` | packets forwarded |
| 0x408 | `fcscnt` | dropped: bad FCS or receive error |
| 0x40C | `l2cnt` | dropped: another destination MAC, or not IPv4 |
| 0x410 | `hdrcnt` | dropped: RFC 1812 header checks |
| 0x414 | `ttlcnt` | dropped: TTL ran out |
| 0x418 | `routecnt` | dropped: no matching route |
| 0x41C | `longcnt` | dropped: frame longer than the buffer |
| 0x420 | `busycnt` | dropped: the port still held an unsent packet |

A MAC address is written with its first byte on the wire in the highest bits.

## Parameters

| Parameter | Default | Range | Meaning |
| :--: | :--: | :--: | :-- |
| `ports` | 4 | 2–4 | RMII ports |
| `routes` | 8 | 2–16 | route table entries |
| `mtu` | 256 | 64–512 | frame buffer per port in bytes, FCS not included |

Not implemented: ICMP (Time Exceeded, Destination Unreachable, Parameter Problem), ARP (next hop MACs are written into the route table), an address of the router's own and local delivery, fragmentation and per-port MTUs, IP options processing such as source routing, multicast and broadcast forwarding, IPv6, VLANs, routing by type of service, and output queues. Buffers are flip-flops, at roughly 90 µm² a byte, so `mtu` stops at 512: four full-size 1518-byte buffers would be larger than a whole reference SoC and need an SRAM macro instead.

## Specification sources

The specifications this IP is implemented against, with their links, digests and the clause-by-clause comparison, are kept on the [`spec` branch](https://github.com/Tape-Out/erouter/tree/spec).

## License

Mulan PSL v2.
