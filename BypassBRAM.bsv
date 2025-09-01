import Vector::*;
import FIFOF::*;
import GetPut::*;
import BRAMCore::*;
import BRAM::*;

// Provides a 2-port BRAM interface scheduled portA.request.put < portB.request.put
// If portA is given a write request and portB is given a read request at the same cycle,
// the response at portB will be the data written by A if the addresses match
module mkBypassBRAM(BRAM2Port#(a, t)) provisos (Bits#(a, l), Bits#(t, tSz));

  Integer memSize = 2 ** valueOf(l);
  BRAM_DUAL_PORT#(Bit#(l), t)          memory    <- mkBRAMCore2(memSize, False);

  // holds whether pending request is a read or a write
  FIFOF#(Bool)                         pendingA  <- mkUGLFIFOF;
  Reg#(Maybe#(t))                      midA[3]   <- mkCReg(3, tagged Invalid);
  FIFOF#(t)                            respA     <- mkUGFIFOF;
  // holds whether pending request is a read or a write
  FIFOF#(Bool)                         pendingB  <- mkUGLFIFOF;
  Reg#(Maybe#(t))                      midB[3]   <- mkCReg(3, tagged Invalid);
  FIFOF#(t)                            respB     <- mkUGFIFOF;
  // data to bypass
  Reg#(Maybe#(t))                      bypass    <- mkReg(tagged Invalid);
  RWire#(BRAMRequest#(a, t))           reqA      <- mkRWire;
  RWire#(BRAMRequest#(a, t))           reqB      <- mkRWire;
  RWire#(void)                         clearA    <- mkRWire;
  RWire#(void)                         clearB    <- mkRWire;

  // clearPendingA < clearPendingB < portA.request.put < portB.request.put < canonicalize
  (* fire_when_enabled, no_implicit_conditions *)
  rule canonicalize;
    let isClearA = isValid(clearA.wget);
    let isClearB = isValid(clearB.wget);
    let isReqA = isValid(reqA.wget);
    let isReqB = isValid(reqB.wget);
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
    if (isClearA) begin
      pendingA.clear;
      midA[2] <= tagged Invalid;
      respA.clear;
    end else if (isReqA) begin
      pendingA.enq(wrA);
    end

    if (isClearB) begin
      pendingB.clear;
      midB[2] <= tagged Invalid;
      respB.clear;
    end else if (isReqB) begin
      pendingB.enq(wrB);
    end
  endrule

  (* fire_when_enabled, no_implicit_conditions *)
  rule clearPendingA; // never drops a read
    if (pendingA.notEmpty) begin
      if (!pendingA.first) // midA[0] should be Invalid
        midA[0] <= tagged Valid memory.a.read;
      pendingA.deq;
    end
  endrule

  (* fire_when_enabled, no_implicit_conditions *)
  rule clearMidA;
    if (respA.notFull &&& midA[1] matches tagged Valid .d) begin
      respA.enq(d);
      midA[1] <= tagged Invalid;
    end
  endrule

  (* fire_when_enabled, no_implicit_conditions *)
  rule clearPendingB; // never drops a read
    if (pendingB.notEmpty) begin // midB[0] should be Invalid
      if (!pendingB.first) begin
        if (bypass matches tagged Valid .d)
          midB[0] <= tagged Valid d;
        else
          midB[0] <= tagged Valid memory.b.read;
      end
      pendingB.deq;
    end
  endrule

  (* fire_when_enabled, no_implicit_conditions *)
  rule clearMidB;
    if (respB.notFull &&& midB[1] matches tagged Valid .d) begin
      respB.enq(d);
      midB[1] <= tagged Invalid;
    end
  endrule

  interface BRAMServer portA;
    interface Put request;
      method Action put(BRAMRequest#(a, t) req) if (pendingA.notFull && !isValid(midA[2]));
        reqA.wset(req);
      endmethod
    endinterface
    interface Get response;
      method ActionValue#(t) get if (respA.notEmpty);
        let resp = respA.first;
        respA.deq;
        return resp;
      endmethod
    endinterface
  endinterface

  interface BRAMServer portB;
    interface Put request;
      method Action put(BRAMRequest#(a, t) req) if (pendingA.notFull || !isValid(midB[2]));
        reqB.wset(req);
      endmethod
    endinterface
    interface Get response;
      method ActionValue#(t) get if (respB.notEmpty);
        let resp = respB.first;
        respB.deq;
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

