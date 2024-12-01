import Randomizable::*;
import CoalTree::*;
import MergeTree::*;
import VectorMem::*;
import Vector::*;

typedef 32 VecWidth;
typedef UInt#(1) TestData;

function Ordering comp (TestData x, TestData y) = compare(pack(x), pack(y));

(* synthesize *)
module coalTree(CoalTree#(VecWidth, TestData));
  CoalTree#(VecWidth, TestData) c <- mkCoalTree(comp);
  return c;
endmodule

(* synthesize *)
module mergeTree(MergeTree#(VecWidth, TestData));
  MergeTree#(VecWidth, TestData) m <- mkMergeTree;
  return m;
endmodule

(* synthesize *)
module vectorMem(VecMemoryServer#(VecWidth, 32, 32));
  let dummy <- mkDummyMemoryServer;
  let ret <- mkVecMemoryServer(dummy);
  return ret;
endmodule

(* synthesize *)
module mkTop(Empty);
  let cTree <- coalTree;
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
      let e <- cTree.enq(v);
      inCount <= inCount + 1;
    end else if (inCount == threshold) begin
      let e <- cTree.enq(replicate(tagged Invalid)); // mark the end
    end
  endrule

  (* fire_when_enabled *)
  rule test;
    let notEmpty = cTree.notEmpty;
    let res = notEmpty ? tpl_1(cTree.first) : tagged Invalid;
    case (res) matches
      tagged Invalid:
        if (notEmpty && inCount == threshold) $finish;
      tagged Valid .x: begin
        $display(fshow("Deq: ") + fshow(x));
        cTree.deq;
      end
    endcase
  endrule
endmodule
