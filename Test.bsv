import CoalTree::*;
import Vector::*;

typedef 32 VecWidth;

(* synthesize *)
module mkTop(Empty);
  CoalTree#(VecWidth, UInt#(16)) tree <- mkCoalTree;
  Reg#(Maybe#(CoalReq#(VecWidth, UInt#(16)))) out <- mkReg(tagged Invalid);
  Reg#(UInt#(32)) inCount <- mkReg(0);
  Reg#(Bool) started <- mkReg(False);

  (* fire_when_enabled *)
  rule put;
    Vector#(VecWidth, Maybe#(UInt#(16))) v = replicate(tagged Invalid);
    case (inCount) matches
      0: begin
        v[0] = tagged Valid 1;
        v[2] = tagged Valid 1;
        v[3] = tagged Valid 4;
      end
      1: begin
        v[0] = tagged Valid 5;
        v[1] = tagged Valid 0;
        v[2] = tagged Valid 3;
        v[3] = tagged Valid 4;
      end
      2: begin
        v[0] = tagged Valid 3;
      end
      default: noAction;
    endcase
    tree.enq(v);
    inCount <= inCount + 1;
  endrule

  (* fire_when_enabled *)
  rule get(!isValid(out));
    let res = tree.notEmpty ? tpl_1(tree.first) : tagged Invalid;
    if (isValid(res)) started <= True;
    else if (started) $finish;
    out <= res;
    tree.deq;
  endrule

  (* fire_when_enabled *)
  rule test(isValid(out));
    $display(fshow(fromMaybe(?, out)));
    out <= tagged Invalid;
  endrule
endmodule
