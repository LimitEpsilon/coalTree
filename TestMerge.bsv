import Randomizable::*;
import MergeTree::*;
import FIFOF::*;
import Vector::*;

typedef 32 VecWidth;
typedef UInt#(4) TestData;
typedef 8 MemWidth;

(* synthesize *)
module mergeTree(MergeTree#(VecWidth, TestData));
  let m <- mkMergeTree;
  return m;
endmodule

(* noinline *)
function Tuple2#(Maybe#(Bit#(TLog#(VecWidth))), Vector#(sn, Bool))
  arb(Vector#(VecWidth, Maybe#(TestData)) in, Vector#(sn, Bool) prio)
  provisos (Add#(1, sn, VecWidth)) = treeArb(in, prio);

(* synthesize *)
module mkTopMerge(Empty);
  Reg#(Vector#(TSub#(VecWidth, 1), Bool)) prios <- mkReg(replicate(True));
  Vector#(VecWidth, RWire#(TestData)) in <- replicateM(mkRWire);
  Vector#(VecWidth, FIFOF#(TestData)) datas <- replicateM(mkLFIFOF);
  Randomize#(Bool) randomEnq <- mkGenericRandomizer;
  Randomize#(Vector#(VecWidth, Bool)) randomInv <- mkGenericRandomizer;
  Randomize#(Vector#(VecWidth, TestData)) randomData <- mkGenericRandomizer;
  Reg#(UInt#(32)) inCount <- mkReg(0);
  Reg#(UInt#(32)) cycle <- mkReg(0);
  UInt#(32) threshold = 1;
  RWire#(void) finish <- mkRWire;

  Vector#(VecWidth, Maybe#(TestData)) asserted;
  for (Integer i = 0; i < valueOf(VecWidth); i = i + 1) begin
    asserted[i] = in[i].wget;
  end
  match {.selected, .nprio} = arb(asserted, prios);

  (* fire_when_enabled *)
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

  for (Integer i = 0; i < valueOf(VecWidth); i = i + 1) begin
    (* fire_when_enabled *)
    rule do_assert;
      in[i].wset(datas[i].first);
    endrule
  end

  (* fire_when_enabled *)
  rule do_deq;
    if (selected matches tagged Valid .idx) begin
      $display(fshow("Deq: ") + fshow(datas[idx].first));
      datas[idx].deq;
    end
    prios <= nprio;
  endrule
endmodule
