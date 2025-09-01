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
  Randomize#(Bool) randomWriteA <- mkGenericRandomizer;
  Randomize#(Bool) randomWriteB <- mkGenericRandomizer;
  Randomize#(Addr) randomAddrA <- mkGenericRandomizer;
  Randomize#(Addr) randomAddrB <- mkGenericRandomizer;
  Randomize#(Data) randomDataA <- mkGenericRandomizer;
  Randomize#(Data) randomDataB <- mkGenericRandomizer;
  Randomize#(Bool) randomGetA <- mkGenericRandomizer;
  Randomize#(Bool) randomGetB <- mkGenericRandomizer;

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
    if (cycle == 0) begin
      randomWriteA.cntrl.init;
      randomWriteB.cntrl.init;
      randomAddrA.cntrl.init;
      randomAddrB.cntrl.init;
      randomDataA.cntrl.init;
      randomDataB.cntrl.init;
      randomGetA.cntrl.init;
      randomGetB.cntrl.init;
    end
    $display("Cycle: %d over --------------------------------------------------", cycle);
    cycle <= cycle + 1;
  endrule

  (* fire_when_enabled *)
  rule putA;
    let writeA <- randomWriteA.next;
    let addrA <- randomAddrA.next;
    let dataA <- randomDataA.next;
    let reqA = BRAMRequest {write: writeA, address: addrA, datain: dataA};

    m.portA.request.put(reqA);
    $display("PortA request: %s, address %d, data %d", writeA ? "write" : "read", addrA, dataA);
  endrule

  (* fire_when_enabled *)
  rule putB;
    let writeB <- randomWriteB.next;
    let addrB <- randomAddrB.next;
    let dataB <- randomDataB.next;
    let reqB = BRAMRequest {write: writeB, address: addrB, datain: dataB};

    m.portB.request.put(reqB);
    $display("PortB request: %s, address %d, data %d", writeB ? "write" : "read", addrB, dataB);
  endrule

  (* fire_when_enabled *)
  rule testA;
    let doResp <- randomGetA.next;
    if (doResp) begin
      let resp <- m.portA.response.get;
      countA <= countA + 1;
      $display("PortA response: %d", resp);
    end
  endrule

  (* fire_when_enabled *)
  rule testB;
    let doResp <- randomGetB.next;
    if (doResp) begin
      let resp <- m.portB.response.get;
      countB <= countB + 1;
      $display("PortB response: %d", resp);
    end
  endrule

  (* fire_when_enabled, no_implicit_conditions *)
  rule do_finish;
    if (countA > threshold && countB > threshold) $finish;
  endrule
endmodule
