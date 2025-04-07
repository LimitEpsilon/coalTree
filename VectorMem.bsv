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
  CoalTree#(n, MemoryRequest#(a, d)) c <- mkCoalTree(comp);
  Vector#(n, FIFOF#(MemoryResponse#(d))) out <- replicateM(mkFIFOF);

  (* fire_when_enabled *)
  rule do_mem_req;
    match {.req, .*} = c.first;
    case (pack(req.mask) == 0) matches
      True: noAction;
      False: begin
        m.request.put(req.req);
        Vector#(n, Bool) v = newVector;
        for (Integer i = 0; i < valueOf(n); i = i + 1) begin
          v[i] = unpack(req.mask[i]);
        end
        if (!req.req.write) respMasks.enq(v);
      end
    endcase
    c.deq;
  endrule

  (* fire_when_enabled *)
  rule do_mem_resp;
    let resp <- m.response.get;
    let respMask = respMasks.first;
    for (Integer i = 0; i < valueOf(n); i = i + 1) begin
      if (respMask[i]) out[i].enq(resp);
    end
    respMasks.deq;
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
      let outMask = outMasks.first;
      Vector#(n, Maybe#(Bit#(d))) ret = replicate(tagged Invalid);
      for (Integer i = 0; i < valueOf(n); i = i + 1) begin
        if (outMask[i]) begin
          ret[i] = tagged Valid out[i].first.data;
          out[i].deq;
        end
      end
      outMasks.deq;
      return VecMemoryResponse {datas: ret};
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

