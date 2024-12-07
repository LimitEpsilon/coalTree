import Randomizable::*;
import MergeTree::*;
import FIFOF::*;
import Vector::*;

typedef 32 VecWidth;
typedef UInt#(1) TestData;
typedef 8 MemWidth;

(* synthesize *)
module mergeTree(MergeTree#(VecWidth, TestData));
  let m <- mkMergeTree;
  return m;
endmodule

(* synthesize *)
module mkTopMerge(Empty);
  let mTree <- mergeTree;
  Vector#(VecWidth, FIFOF#(TestData)) datas <- replicateM(mkLFIFOF);
  Randomize#(Bool) randomEnq <- mkGenericRandomizer;
  Randomize#(Vector#(VecWidth, Bool)) randomInv <- mkGenericRandomizer;
  Randomize#(Vector#(VecWidth, TestData)) randomData <- mkGenericRandomizer;
  Reg#(UInt#(32)) inCount <- mkReg(0);
  Reg#(UInt#(32)) cycle <- mkReg(0);
  UInt#(32) threshold = 1;
  RWire#(void) finish <- mkRWire;

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
    if (cycle > 100) $finish;
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
      for (Integer i = 0; i < valueOf(VecWidth); i = i + 1) begin
        if (!inv[i]) datas[i].enq(data[i]);
      end
      $display(fshow("Enq: ") + fshow(v));
      inCount <= inCount + 1;
    end else if (inCount == threshold) begin
      finish.wset(?);
    end
  endrule

  (* fire_when_enabled *)
  rule do_assert;
    for (Integer i = 0; i < valueOf(VecWidth); i = i + 1) begin
      if (datas[i].notEmpty) begin
        let data = datas[i].first;
        mTree.iport[i].asrt(data);
      end
    end
  endrule

  (* fire_when_enabled *)
  rule do_deq;
    for (Integer i = 0; i < valueOf(VecWidth); i = i + 1) begin
      if (datas[i].notEmpty && mTree.iport[i].selected) datas[i].deq;
    end
  endrule

  (* fire_when_enabled *)
  (* no_implicit_conditions *)
  rule test;
    let x = mTree.first;
    if (x matches tagged Valid .y) begin
      mTree.select;
      $display(fshow("Deq: ") + fshow(y));
    end
  endrule
endmodule
