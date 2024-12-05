import Randomizable::*;
import ChoiceTree::*;
import CoalTree::*;
import MergeTree::*;
import VectorMem::*;
import Memory::*;
import ClientServer::*;
import GetPut::*;
import Vector::*;

typedef 32 VecWidth;
typedef UInt#(1) TestData;
typedef 8 MemWidth;

(* synthesize *)
module vectorMem(VecMemoryServer#(VecWidth, MemWidth, MemWidth));
  let dummy <- mkDummyMemoryServer;
  let ret <- mkVecMemoryServer(dummy);
  return ret;
endmodule

(* synthesize *)
module mkTopMem(Empty);
  let m <- vectorMem;
  Randomize#(Bool) randomEnq <- mkGenericRandomizer;
  Randomize#(Vector#(VecWidth, Bool)) randomInv <- mkGenericRandomizer;
  Randomize#(Vector#(VecWidth, TestData)) randomData <- mkGenericRandomizer;
  Reg#(UInt#(32)) inCount <- mkReg(0);
  Reg#(UInt#(32)) cycle <- mkReg(0);
  UInt#(32) threshold = 32;
  Reg#(Bool) finish <- mkReg(False);

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

    function Bit#(MemWidth) g(TestData x) = extend(pack(x));
    m.request.put(VecMemoryRequest {
      write: !doEnq,
      addresses: map(g, data),
      datas: map(g, data),
      mask: inv
    });

    if (inCount < threshold && any(id, inv) && doEnq) begin
      $display(fshow("Enq: ") + fshow(v));
      $display(fshow("First valid index: ") + fshow(treeChoice(v)));
      inCount <= inCount + 1;
    end else if (inCount == threshold) begin
      finish <= True;
    end
  endrule

  (* fire_when_enabled *)
  rule test;
    let mRes <- m.response.get;
    $display(fshow("Deq: ") + fshow(mRes));
    if (finish) $finish;
  endrule
endmodule
