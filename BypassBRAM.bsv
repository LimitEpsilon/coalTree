import Vector::*;
import GetPut::*;
import BRAMCore::*;
import BRAM::*;

// Provides a 2-port BRAM interface scheduled portA.request.put < portB.request.put
// If portA is given a write request and portB is given a read request in the same cycle,
// the response at portB will be the data written by A if the addresses match
module mkBypassBRAM(BRAM2Port#(a, t)) provisos (Bits#(a, l), Bits#(t, tSz));
  Integer memSize = 2 ** valueOf(l);
  BRAM_DUAL_PORT#(Bit#(l), t)          memory    <- mkBRAMCore2(memSize, False);

  // holds whether pending request is a read or a write
  Reg#(Maybe#(Bool))                   pendingA  <- mkReg(tagged Invalid);
  Reg#(Maybe#(t))                      midA[3]   <- mkCReg(3, tagged Invalid);
  Reg#(Maybe#(t))                      respA[2]  <- mkCReg(2, tagged Invalid);
  // holds whether pending request is a read or a write
  Reg#(Maybe#(Bool))                   pendingB  <- mkReg(tagged Invalid);
  Reg#(Maybe#(t))                      midB[3]   <- mkCReg(3, tagged Invalid);
  Reg#(Maybe#(t))                      respB[2]  <- mkCReg(2, tagged Invalid);
  // data to bypass
  Reg#(Maybe#(t))                      bypass    <- mkReg(tagged Invalid);
  RWire#(BRAMRequest#(a, t))           reqA      <- mkRWire;
  RWire#(BRAMRequest#(a, t))           reqB      <- mkRWire;
  RWire#(void)                         clearA    <- mkRWire;
  RWire#(void)                         clearB    <- mkRWire;
  RWire#(void)                         deqA      <- mkRWire;
  RWire#(void)                         deqB      <- mkRWire;

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

    // bypass register
    if (isReqA && wrA && !isClearB && isReqB && !wrB && addrEq)
      bypass <= tagged Valid dataA;
    else
      bypass <= tagged Invalid;

    // FIFOs
    pendingA <= isReqA ? tagged Valid wrA : tagged Invalid;
    if (isClearA) midA[2] <= tagged Invalid;
    if (isClearA || isDeqA) respA[1] <= tagged Invalid;

    pendingB <= isReqB ? tagged Valid wrB : tagged Invalid;
    if (isClearB) midB[2] <= tagged Invalid;
    if (isClearB || isDeqB) respB[1] <= tagged Invalid;
  endrule

  (* fire_when_enabled, no_implicit_conditions *)
  rule clear_pendingA; // never drops a read
    if (pendingA matches tagged Valid .wr) // midA[0] should be Invalid
      if (!wr)
        midA[0] <= tagged Valid memory.a.read;
  endrule

  (* fire_when_enabled, no_implicit_conditions *)
  rule clear_midA;
    if (!isValid(respA[0]) &&& midA[1] matches tagged Valid .d) begin
      respA[0] <= tagged Valid d;
      midA[1] <= tagged Invalid;
    end
  endrule

  (* fire_when_enabled, no_implicit_conditions *)
  rule clear_pendingB; // never drops a read
    if (pendingB matches tagged Valid .wr) // midB[0] should be Invalid
      if (!wr)
        if (bypass matches tagged Valid .d)
          midB[0] <= tagged Valid d;
        else
          midB[0] <= tagged Valid memory.b.read;
  endrule

  (* fire_when_enabled, no_implicit_conditions *)
  rule clear_midB;
    if (!isValid(respB[0]) &&& midB[1] matches tagged Valid .d) begin
      respB[0] <= tagged Valid d;
      midB[1] <= tagged Invalid;
    end
  endrule

  interface BRAMServer portA;
    interface Put request;
      method Action put(BRAMRequest#(a, t) req) if (!isValid(midA[2]));
        reqA.wset(req);
      endmethod
    endinterface
    interface Get response;
      method ActionValue#(t) get if (isValid(respA[1]));
        let resp = fromMaybe(?, respA[1]);
        deqA.wset(?);
        return resp;
      endmethod
    endinterface
  endinterface

  interface BRAMServer portB;
    interface Put request;
      method Action put(BRAMRequest#(a, t) req) if (!isValid(midB[2]));
        reqB.wset(req);
      endmethod
    endinterface
    interface Get response;
      method ActionValue#(t) get if (isValid(respB[1]));
        let resp = fromMaybe(?, respB[1]);
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

