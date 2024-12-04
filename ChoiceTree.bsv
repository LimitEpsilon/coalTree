// Adapted from https://github.com/mtikekar/advanced_bsv
import Vector::*;

// returns the index of the first valid element
typeclass ChoiceTree#(numeric type n, type t);
  function Maybe#(Bit#(TLog#(n))) treeChoice(Vector#(n, Maybe#(t)) v);
endtypeclass

instance ChoiceTree#(1, t) provisos (Bits#(t, tSz));
  // Base instance of 1-long vector
  function treeChoice(v) = isValid(v[0]) ? tagged Valid 0'b0 : tagged Invalid;
endinstance

instance ChoiceTree#(n, t) provisos (
  Mul#(hn, 2, n), Add#(hn, _, n), ChoiceTree#(hn, t), Bits#(t, tSz)
);
  // General case
  function treeChoice(v);
    Vector#(hn, Maybe#(t)) v1 = take(v);
    Vector#(hn, Maybe#(t)) v2 = takeTail(v);
    let idx1 = treeChoice(v1);
    let idx2 = treeChoice(v2);
    return
      case (idx1) matches
        tagged Invalid:
          case (idx2) matches
            tagged Invalid: tagged Invalid;
            tagged Valid .i2: tagged Valid ({ 1'b1, i2 });
          endcase
        tagged Valid .i1: tagged Valid ({ 1'b0, i1 });
      endcase;
  endfunction
endinstance
