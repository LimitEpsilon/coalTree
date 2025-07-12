import Randomizable::*;
import Stack::*;
import FIFOF::*;
import Vector::*;

typedef 32 VecWidth;
typedef UInt#(4) TestData;
typedef 8 MemWidth;

(* synthesize *)
module mkTopStack(Empty);
  Randomize#(TestData) randTest <- mkGenericRandomizer;
  Randomize#(Bool) doPop <- mkGenericRandomizer;
  Randomize#(Bool) doPush <- mkGenericRandomizer;
  Stack#(4, TestData) stack <- mkStack(True, True);
  Reg#(UInt#(4)) times <- mkReg(0);
  Reg#(Bool) init <- mkReg(False);
  Reg#(Bool) finish <- mkReg(False);
  Reg#(UInt#(32)) cycle <- mkReg(0);

  rule print_cycle;
    $display("Cycle: %d", cycle);
    cycle <= cycle + 1;
  endrule

  rule init_rand(!init);
    randTest.cntrl.init;
    doPop.cntrl.init;
    doPush.cntrl.init;
    init <= True;
  endrule

  rule do_pop(init && !finish);
    let b <- doPop.next;
    if (b) stack.pop;
  endrule

  rule do_push(init && !finish);
    let b <- doPush.next;
    let x <- randTest.next;
    if (b) begin
      stack.push(x);
      finish <= times == 15;
      times <= times + 1;
    end
  endrule

  rule finish_test(finish);
    $finish;
  endrule
endmodule
