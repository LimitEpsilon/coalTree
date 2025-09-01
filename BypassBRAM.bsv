import Vector::*;
import GetPut::*;
import BRAMCore::*;
import BRAM::*;

// Provides a 2-port BRAM interface scheduled portA.request.put < portB.request.put
// If portA is given a write request and portB is given a read request in the same cycle,
// the response at portB will be the data written by A if the addresses match
module mkBypassBRAM(BRAM2Port#(a, t)) provisos (Bits#(a, l), Bits#(t, tSz));
  Integer memSize = 2 ** valueOf(l);
  BRAM_DUAL_PORT#(Bit#(l), t) memory         <- mkBRAMCore2(memSize, False);

  // holds whether pending request is a read or a write
  Reg#(Bool)                  pendingAValid  <- mkReg(False);
  Reg#(Bool)                  pendingA       <- mkRegU;
  Reg#(Bool)                  midAValid[3]   <- mkCReg(3, False);
  Reg#(t)                     midA[2]        <- mkCRegU(2);
  Reg#(Bool)                  respAValid[2]  <- mkCReg(2, False);
  Reg#(t)                     respA[2]       <- mkCRegU(2);
  // holds whether pending request is a read or a write
  Reg#(Bool)                  pendingBValid  <- mkReg(False);
  Reg#(Bool)                  pendingB       <- mkRegU;
  Reg#(Bool)                  midBValid[3]   <- mkCReg(3, False);
  Reg#(t)                     midB[2]        <- mkCRegU(2);
  Reg#(Bool)                  respBValid[2]  <- mkCReg(2, False);
  Reg#(t)                     respB[2]       <- mkCRegU(2);
  // data to bypass
  Reg#(Bool)                  bypassValid    <- mkReg(False);
  Reg#(t)                     bypass         <- mkRegU;
  RWire#(BRAMRequest#(a, t))  reqA           <- mkRWire;
  RWire#(BRAMRequest#(a, t))  reqB           <- mkRWire;
  RWire#(void)                clearA         <- mkRWire;
  RWire#(void)                clearB         <- mkRWire;
  RWire#(void)                deqA           <- mkRWire;
  RWire#(void)                deqB           <- mkRWire;

  // clear_pendingA < clear_pendingB < portA.request.put < portB.request.put < canonicalize
  (* fire_when_enabled, no_implicit_conditions *)
  rule canonicalize;
    let isReqA = isValid(reqA.wget);
    let isReqB = isValid(reqB.wget);
    let isClearA = isValid(clearA.wget);
    let isClearB = isValid(clearB.wget);
    let isDeqA = isValid(deqA.wget);
    let isDeqB = isValid(deqB.wget);

    match BRAMRequest {
      write: .wrA, address: .addrA, datain: .dataA
    } = fromMaybe(?, reqA.wget);
    match BRAMRequest {
      write: .wrB, address: .addrB, datain: .dataB
    } = fromMaybe(?, reqB.wget);

    let addrEq = pack(addrA) == pack(addrB);
    let writeB = isReqB && wrB;
    let writeA = isReqA && wrA && (!writeB || !addrEq);

    // request to memory
    memory.a.put(writeA, pack(addrA), dataA);
    memory.b.put(writeB, pack(addrB), dataB);

    // bypass when write to A and read to B with same addresses
    bypassValid <= isReqA && wrA && !isClearB && isReqB && !wrB && addrEq;
    bypass <= dataA;

    // FIFOs
    pendingAValid <= isReqA;
    pendingA <= wrA;
    if (isClearA) midAValid[2] <= False;
    if (isClearA || isDeqA) respAValid[1] <= False;

    pendingBValid <= isReqB;
    pendingB <= wrB;
    if (isClearB) midBValid[2] <= False;
    if (isClearB || isDeqB) respBValid[1] <= False;
  endrule

  (* fire_when_enabled, no_implicit_conditions *)
  rule clear_pendingA; // never drops a read
    if (pendingAValid && !pendingA) begin // midA[0] should be Invalid
      midAValid[0] <= True;
      midA[0] <= memory.a.read;
    end
  endrule

  (* fire_when_enabled, no_implicit_conditions *)
  rule clear_midA;
    if (!respAValid[0] && midAValid[1]) begin
      respAValid[0] <= True;
      respA[0] <= midA[1];
      midAValid[1] <= False;
    end
  endrule

  (* fire_when_enabled, no_implicit_conditions *)
  rule clear_pendingB; // never drops a read
    if (pendingBValid && !pendingB) begin // midB[0] should be Invalid
      midBValid[0] <= True;
      midB[0] <= bypassValid ? bypass : memory.b.read;
    end
  endrule

  (* fire_when_enabled, no_implicit_conditions *)
  rule clear_midB;
    if (!respBValid[0] && midBValid[1]) begin
      respBValid[0] <= True;
      respB[0] <= midB[1];
      midBValid[1] <= False;
    end
  endrule

  interface BRAMServer portA;
    interface Put request;
      method Action put(BRAMRequest#(a, t) req) if (!midAValid[2]);
        reqA.wset(req);
      endmethod
    endinterface
    interface Get response;
      method ActionValue#(t) get if (respAValid[1]);
        let resp = respA[1];
        deqA.wset(?);
        return resp;
      endmethod
    endinterface
  endinterface

  interface BRAMServer portB;
    interface Put request;
      method Action put(BRAMRequest#(a, t) req) if (!midBValid[2]);
        reqB.wset(req);
      endmethod
    endinterface
    interface Get response;
      method ActionValue#(t) get if (respBValid[1]);
        let resp = respB[1];
        deqB.wset(?);
        return resp;
      endmethod
    endinterface
  endinterface

  method Action portAClear;
    clearA.wset(?);
  endmethod
  method Action portBClear;
    clearB.wset(?);
  endmethod
endmodule

