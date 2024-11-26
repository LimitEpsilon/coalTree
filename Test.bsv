import Randomizable::*;
import CoalTree::*;
import Vector::*;

typedef 32 VecWidth;
typedef UInt#(2) TestData;

(* synthesize *)
module coalTree(CoalTree#(VecWidth, TestData));
  CoalTree#(VecWidth, TestData) c <- mkCoalTree;
  method enq = c.enq;
  method notEmpty = c.notEmpty;
  method deq = c.deq;
  method first = c.first;
endmodule

(* synthesize *)
module mkTop(Empty);
  let tree <- coalTree;
  Randomize#(Bool) randomEnq <- mkGenericRandomizer;
  Randomize#(Vector#(VecWidth, Bool)) randomInv <- mkGenericRandomizer;
  Randomize#(Vector#(VecWidth, TestData)) randomData <- mkGenericRandomizer;
  let finish <- mkReg(False);
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
    end
    $display("Cycle: %d over --------------------------------------------------", cycle);
    cycle <= cycle + 1;
  endrule

  (* fire_when_enabled *)
  rule put(inCount < threshold);
    function Maybe#(TestData) f(Bool inv, TestData data) =
      inv ? tagged Invalid : tagged Valid data;
    let doEnq <- randomEnq.next;
    let inv <- randomInv.next;
    let data <- randomData.next;
    let v = zipWith(f, inv, data);
    if (doEnq) begin
      $display(fshow("Enq: ") + fshow(v));
      tree.enq(v);
      inCount <= inCount + 1;
    end
  endrule

  (* fire_when_enabled *)
  rule test;
    let notEmpty = tree.notEmpty;
    let res = notEmpty ? tpl_1(tree.first) : tagged Invalid;
    if (notEmpty) begin
      $display(fshow("Deq: ") + fshow(res));
      tree.deq;
    end else if (inCount == threshold)
      if (!finish) begin
        finish <= True;
      end else begin
        $finish;
      end
  endrule
endmodule
