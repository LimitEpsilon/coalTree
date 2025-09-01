import Randomizable::*;
import CoalTree::*;
import VectorMem::*;
import Memory::*;
import ClientServer::*;
import GetPut::*;
import Vector::*;
import BRAM::*;

typedef 17 VecWidth;
typedef UInt#(2) TestData;
typedef 8 MemWidth;

function void merge (void x, void y) = x;

(* synthesize *)
module coalTree(CoalTree#(VecWidth, 2, void));
  CoalTree#(VecWidth, 2, void) c <- mkCoalTree(merge);
  return c;
endmodule

(* synthesize *)
module testBRAM(BRAM2Port#(Bit#(1), TestData));
  BRAM_Configure cfg = defaultValue;
  cfg.memorySize = 2;
  let ram <- mkBRAM2Server(cfg);
  return ram;
endmodule

(* synthesize *)
module mkTopCoal(Empty);
  let cTree <- coalTree;
  let ram <- testBRAM;
  Randomize#(Bool) randomEnq <- mkGenericRandomizer;
  Randomize#(Vector#(VecWidth, Bool)) randomInv <- mkGenericRandomizer;
  Randomize#(Vector#(VecWidth, TestData)) randomData <- mkGenericRandomizer;
  Reg#(UInt#(32)) inCount <- mkReg(0);
  Reg#(UInt#(32)) cycle <- mkReg(0);
  UInt#(32) threshold = 32;

  (* fire_when_enabled *)
  (* execution_order = "put, increment" *)
  (* execution_order = "test, increment" *)
  rule increment;
    if (cycle == 0) begin
      randomEnq.cntrl.init;
      randomInv.cntrl.init;
      randomData.cntrl.init;
      ram.portA.request.put(BRAMRequest {
	write: True,
	responseOnWrite: False,
	address: 0,
	datain: 0
      });
      ram.portB.request.put(BRAMRequest {
	write: False,
	responseOnWrite: False,
	address: 0,
	datain: 0
      });
    end else if (cycle == 1) begin
      let r <- ram.portB.response.get;
      $display("%d", r);
    end
    $display("Cycle: %d over --------------------------------------------------", cycle);
    cycle <= cycle + 1;
  endrule

  (* fire_when_enabled *)
  rule put;
    function Maybe#(KV#(2, void)) f(Bool inv, TestData data) =
      inv ? tagged Invalid : tagged Valid KV {key: pack(data), val: ?};
    let doEnq <- randomEnq.next;
    let inv <- randomInv.next;
    let data <- randomData.next;
    let v = zipWith(f, inv, data);

    if (inCount < threshold && any(id, inv) && doEnq) begin
      $display(fshow("Enq: ") + fshow(v));
      let e <- cTree.enq(v);
      inCount <= inCount + 1;
    end else if (inCount == threshold) begin
      let e <- cTree.enq(replicate(tagged Invalid)); // mark the end
    end
  endrule

  (* fire_when_enabled *)
  rule test(cTree.notEmpty);
    let res = cTree.first;
    $display(fshow("Deq: ") + fshow(res));
    if (res.mask == 0 && inCount == threshold) $finish;
    cTree.deq;
  endrule
endmodule
