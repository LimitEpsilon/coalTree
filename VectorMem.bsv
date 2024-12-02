import Vector::*;
import FIFOF::*;
import GetPut::*;
import ClientServer::*;
import Memory::*;
import CoalTree::*;

typedef struct {
  Bool write;
  Vector#(n, Bit#(a)) addresses;
  Vector#(n, Bit#(d)) datas;
  Vector#(n, Bool) mask;
} VecMemoryRequest#(numeric type n, numeric type a, numeric type d)
deriving (Bits, Eq, FShow);

typedef struct {
  Vector#(n, Maybe#(Bit#(d))) datas;
} VecMemoryResponse#(numeric type n, numeric type d)
deriving (Bits, Eq, FShow);

typedef Server#(VecMemoryRequest#(n, a, d), VecMemoryResponse#(n, d))
  VecMemoryServer#(numeric type n, numeric type a, numeric type d);

function Ordering comp(MemoryRequest#(a, d) x, MemoryRequest#(a, d) y) =
  compare(x.address, y.address);

module mkVecMemoryServer(MemoryServer#(a, d) m, VecMemoryServer#(n, a, d) ifc)
  provisos (Add#(_, 1, TDiv#(d, 8)), Coalescer#(n, MemoryRequest#(a, d)));
  FIFOF#(Vector#(n, Bool)) outMasks <- mkFIFOF;
  FIFOF#(Vector#(n, Bool)) respMasks <- mkFIFOF;
  Reg#(Vector#(n, Bool)) leftover <- mkReg(replicate(False));
  Reg#(Bool) cleared[2] <- mkCReg(2, True);
  Reg#(Vector#(n, Maybe#(Bit#(d)))) outBuf <- mkReg(replicate(tagged Invalid));
  CoalTree#(n, MemoryRequest#(a, d)) c <- mkCoalTree(comp);
  FIFOF#(VecMemoryResponse#(n, d)) out <- mkFIFOF;

  Bool isLeftover = any(id, leftover);

  (* fire_when_enabled *)
  rule do_mem_req;
    match {.req, .*} = c.first;
    case (req) matches
      tagged Invalid: noAction;
      tagged Valid .r: begin
        m.request.put(r.req);
        if (!r.req.write) respMasks.enq(r.mask);
      end
    endcase
    c.deq;
  endrule

  (* fire_when_enabled *)
  rule do_mem_resp(isLeftover);
    let resp <- m.response.get;
    let respMask = respMasks.first;
    function Maybe#(Bit#(d)) f(MemoryResponse#(d) l, Bool mask, Maybe#(Bit#(d)) r) =
      mask ? tagged Valid l.data : r;
    function Bool bneg(Bool b) = !b;
    leftover <= zipWith(\&& , leftover, map(bneg, respMask));
    outBuf <= zipWith(f(resp), respMask, outBuf);
    respMasks.deq;
  endrule

  (* fire_when_enabled *)
  rule enq_out(!isLeftover && !cleared[0]);
    out.enq(VecMemoryResponse {datas: outBuf});
    cleared[0] <= True;
  endrule

  (* fire_when_enabled *)
  rule set_leftover(!isLeftover && cleared[1]);
    leftover <= outMasks.first;
    outBuf <= replicate(tagged Invalid);
    outMasks.deq;
    cleared[1] <= False;
  endrule

  interface Put request;
    method Action put(VecMemoryRequest#(n, a, d) vReq);
      function f(mask, addr, data);
        MemoryRequest#(a, d) req = MemoryRequest {
          write: vReq.write,
          byteen: signExtend(1'b1),
          address: addr,
          data: data
        };
        return mask ? tagged Valid req : tagged Invalid;
      endfunction
      let req = zipWith3(f, vReq.mask, vReq.addresses, vReq.datas);
      let e <- c.enq(req);
      if (!vReq.write) outMasks.enq(vReq.mask);
    endmethod
  endinterface

  interface Get response;
    method ActionValue#(VecMemoryResponse#(n, d)) get;
      let resp = out.first;
      out.deq;
      return resp;
    endmethod
  endinterface
endmodule

// For testing
module mkDummyMemoryServer(MemoryServer#(a, d));
  FIFOF#(MemoryRequest#(a, d)) f <- mkFIFOF;

  interface Put request;
    method Action put(MemoryRequest#(a, d) req);
      if (!req.write) f.enq(req);
    endmethod
  endinterface

  interface Get response;
    method ActionValue#(MemoryResponse#(d)) get;
      let resp = MemoryResponse {data: f.first.data};
      f.deq;
      return resp;
    endmethod
  endinterface
endmodule

// TODO:: module mkVecBankedMemoryServer(
//   Vector#(b, MemoryServer#(a, d)) banks,
//   function Bit#(lb) dec_bank(Bit#(la) addr),
//   VecMemoryServer#(n, a, d) ifc
// ) provisos (Log#(a, la), Log#(b, lb));

// TODO:: module mkBurstMemoryServer(
// Given a stream of sorted MemoryRequest#(a, d) and given a memory that
// supports burst read/writes of (m * d) bits (i.e. MemoryServer#(a, md)),
// detect memory requests that fits within a burst.
// If it is a write, use the byteen field of MemoryRequest#(a, m * d)
// to select the valid write data
// ) provisos (Mul#(m, d, md));

