import Vector::*;
import FIFOF::*;
import RegFile::*;
import Randomizable::*;

import BRAM::*;
import GetPut::*;
import ClientServer::*;
import BypassBRAM::*;

typedef Bit#(1) Addr;
typedef Bit#(32) Data;

(* synthesize *)
module mkMyBRAM(BRAM2Port#(Addr, Data));
  let m <- mkBypassBRAM;
  return m;
endmodule

(* synthesize *)
module mkTopBRAM(Empty);
  let m <- mkMyBRAM;
  Vector#(2, Array#(Reg#(Data))) model <- replicateM(mkCRegU(2));
  Reg#(Bool) writeA <- mkReg(True);
  Reg#(Data) dataA <- mkReg(0);
  Reg#(Bool) writeB <- mkReg(True);
  Reg#(Data) dataB <- mkReg(1000);
  Reg#(Bool) getB <- mkReg(False);

  Reg#(Addr) addressA <- mkRegU;
  Reg#(Addr) addressB <- mkRegU;
  Reg#(Bool) failure[2] <- mkCReg(2, False);

  Reg#(UInt#(32)) countA <- mkReg(0);
  Reg#(UInt#(32)) countB <- mkReg(0);
  Reg#(UInt#(32)) cycle <- mkReg(0);
  UInt#(32) threshold = 32;

  (* fire_when_enabled *)
  (* execution_order = "testA, increment" *)
  (* execution_order = "testB, increment" *)
  (* execution_order = "putA, increment" *)
  (* execution_order = "putB, increment" *)
  rule increment;
    $display("Cycle: %d over --------------------------------------------------", cycle);
    cycle <= cycle + 1;
    getB <= !getB;
  endrule

  (* fire_when_enabled *)
  rule putA;
    let addrA = 0;
    let reqA = BRAMRequest {write: writeA, address: addrA, datain: dataA};

    m.portA.request.put(reqA);
    $display("PortA request: %s, address %d, data %d", writeA ? "write" : "read", addrA, dataA);

    if (writeA) begin
      model[addrA][0] <= dataA;
      dataA <= dataA + 1;
    end

    writeA <= !writeA;
    addressA <= addrA;
  endrule

  (* fire_when_enabled *)
  rule putB;
    let addrB = 0;
    let reqB = BRAMRequest {write: writeB, address: addrB, datain: dataB};

    m.portB.request.put(reqB);
    $display("PortB request: %s, address %d, data %d", writeB ? "write" : "read", addrB, dataB);

    if (writeB) begin
      model[addrB][1] <= dataB;
      dataB <= dataB + 1;
    end

    writeB <= !writeB;
    addressB <= addrB;
  endrule

  (* fire_when_enabled *)
  rule testA;
    let resp <- m.portA.response.get;
    let modelResp = model[addressA][0];
    countA <= countA + 1;
    if (resp != modelResp)
      failure[0] <= True;
    $display("%s: PortA response: %d, model response: %d", resp == modelResp ? "SUCCESS" : "FAILED", resp, modelResp);
  endrule

  (* fire_when_enabled *)
  rule testB;
    if (getB) begin
      let resp <- m.portB.response.get;
      let modelResp = model[addressB][0];
      countB <= countB + 1;
      if (resp != modelResp)
        failure[1] <= True;
      $display("%s: PortB response: %d, model response: %d", resp == modelResp ? "SUCCESS" : "FAILED", resp, modelResp);
    end
  endrule

  (* fire_when_enabled, no_implicit_conditions *)
  rule do_finish;
    if (countA > threshold && countB > threshold) begin
      if (failure[0]) $display("FAILED!!!");
      $finish;
    end
  endrule
endmodule
