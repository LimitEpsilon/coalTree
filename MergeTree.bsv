// Adapted from https://github.com/mtikekar/advanced_bsv
import Vector :: *;

interface Assert#(type t);
  method Action asrt(t x);
  method Bool selected;
endinterface

interface MergeTree#(numeric type n, type t);
  interface Vector#(n, Assert#(t)) iport;
  method Action select;
  method Maybe#(t) first;
endinterface

typeclass Merger#(numeric type n, type t);
  module mkMergeTree(MergeTree#(n, t));
endtypeclass

instance Merger#(1, t) provisos (Bits#(t, tSz));
  // Base instance of 1-long vector
  module mkMergeTree(MergeTree#(1, t));
    RWire#(t) in <- mkRWire;
    RWire#(void) sel <- mkRWire;
    Vector#(1, Assert#(t)) i;

    i[0] =
      (interface Assert;
        method asrt = in.wset;
        method selected = isValid(sel.wget);
      endinterface);

    interface iport = i;
    method select = sel.wset(?);
    method first = in.wget;
  endmodule
endinstance

instance Merger#(n, t) provisos (
  Div#(n, 2, hn), Add#(hn, hm, n),
  Merger#(hn, t), Merger#(hm, t),
  Bits#(t, tSz)
);

  // General case
  module mkMergeTree(MergeTree#(n, t));
    // two subtrees
    MergeTree#(hn, t) l <- mkMergeTree;
    MergeTree#(hm, t) r <- mkMergeTree;
    Reg#(Bool) prio <- mkReg(True); // the left tree has priority
    RWire#(t) out <- mkRWire;
    RWire#(void) sel <- mkRWire;

    let lSel = l.first;
    let rSel = r.first;

    (* fire_when_enabled *)
    (* no_implicit_conditions *)
    rule arbitrate_both(isValid(lSel) && isValid(rSel));
      if (prio) out.wset(fromMaybe(?, lSel));
      else out.wset(fromMaybe(?, rSel));
    endrule

    (* fire_when_enabled *)
    (* no_implicit_conditions *)
    rule arbitrate_left(isValid(lSel) && !isValid(rSel));
      out.wset(fromMaybe(?, lSel));
    endrule

    (* fire_when_enabled *)
    (* no_implicit_conditions *)
    rule arbitrate_right(!isValid(lSel) && isValid(rSel));
      out.wset(fromMaybe(?, rSel));
    endrule

    (* fire_when_enabled *)
    (* no_implicit_conditions *)
    rule update_prio(isValid(sel.wget));
      case (tuple2(lSel, rSel)) matches
        {tagged Valid .*, tagged Valid .*}: begin
          if (prio) l.select; else r.select;
          prio <= !prio;
        end
        {tagged Valid .*, tagged Invalid}: begin
          l.select;
          prio <= False;
        end
        {tagged Invalid, tagged Valid .*}: begin
          r.select;
          prio <= True;
        end
        {tagged Invalid, tagged Invalid}: noAction;
      endcase
    endrule

    interface iport = append(l.iport, r.iport);
    method select = sel.wset(?);
    method first = out.wget;
  endmodule
endinstance

