import Randomizable::*;
import CoalTree::*;
import MergeTree::*;
import Vector::*;

typedef 32 VecWidth;
typedef UInt#(1) TestData;

(* synthesize *)
module coalTree(CoalTree#(VecWidth, TestData));
  CoalTree#(VecWidth, TestData) c <- mkCoalTree;
  return c;
endmodule

(* synthesize *)
module mkTop(Empty);
  let tree <- coalTree;
  MergeTree#(VecWidth, TestData) m <- mkMergeTree;
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
    end
    $display("Cycle: %d over --------------------------------------------------", cycle);
    cycle <= cycle + 1;
  endrule

  (* fire_when_enabled *)
  rule put;
    function Maybe#(TestData) f(Bool inv, TestData data) =
      inv ? tagged Invalid : tagged Valid data;
    let doEnq <- randomEnq.next;
    let inv <- randomInv.next;
    let data <- randomData.next;
    let v = zipWith(f, inv, data);
    if (inCount < threshold && any(id, inv) && doEnq) begin
      $display(fshow("Enq: ") + fshow(v));
      let e <- tree.enq(v);
      inCount <= inCount + 1;
    end else if (inCount == threshold) begin
      let e <- tree.enq(replicate(tagged Invalid)); // mark the end
    end
  endrule

  (* fire_when_enabled *)
  rule test;
    let notEmpty = tree.notEmpty;
    let res = notEmpty ? tpl_1(tree.first) : tagged Invalid;
    case (res) matches
      tagged Invalid:
        if (notEmpty && inCount == threshold) $finish;
      tagged Valid .x: begin
        $display(fshow("Deq: ") + fshow(x));
        tree.deq;
      end
    endcase
  endrule
endmodule
