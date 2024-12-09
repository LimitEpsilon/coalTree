// Adapted from https://github.com/mtikekar/advanced_bsv
import Vector :: *;

interface Assert#(type t);
  method Action hold(t x);
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
        method hold = in.wset;
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

typeclass Arbiter#(numeric type n);
  // given: (vector of inputs to be arbitrated, current priority vector)
  // returns: (index that was selected, next priority vector)
  function Tuple2#(Maybe#(Bit#(TLog#(n))), Vector#(TSub#(n, 1), Bool))
    treeArb(Vector#(n, Maybe#(void)) in, Vector#(TSub#(n, 1), Bool) prio);
endtypeclass

instance Arbiter#(1);
  // Base instance of 1-long vector
  function Tuple2#(Maybe#(Bit#(0)), Vector#(0, Bool))
    treeArb(Vector#(1, Maybe#(void)) in, Vector#(0, Bool) prio) =
    tuple2(isValid(in[0]) ? tagged Valid 0'b0 : tagged Invalid, prio);
endinstance

instance Arbiter#(n) provisos (
  Mul#(hn, 2, n), Add#(hn, hn, n), Add#(1, TLog#(hn), TLog#(n)),
  Add#(1, TAdd#(hn, b__), n), Add#(2, a__, n), Arbiter#(hn)
);

  // General case
  function Tuple2#(Maybe#(Bit#(TLog#(n))), Vector#(TSub#(n, 1), Bool))
    treeArb(Vector#(n, Maybe#(void)) in, Vector#(TSub#(n, 1), Bool) prio);
    Vector#(hn, Maybe#(void)) inL = take(in);
    Vector#(hn, Maybe#(void)) inR = takeTail(in);
    Vector#(1, Bool) thisPrio = take(prio);
    Vector#(TSub#(n, 2), Bool) subPrio = takeTail(prio);
    Vector#(TSub#(hn, 1), Bool) prioL = take(subPrio);
    Vector#(TSub#(hn, 1), Bool) prioR = takeTail(subPrio);

    match {.idxL, .nprioL} = treeArb(inL, prioL);
    match {.idxR, .nprioR} = treeArb(inR, prioR);

    Maybe#(Bit#(TLog#(n))) ret = tagged Invalid;

    if (idxL matches tagged Valid .iL) begin
      if (idxR matches tagged Valid .iR) begin
        thisPrio[0] = !thisPrio[0];
        if (prio[0]) begin
          ret = tagged Valid ({0, iL});
          prioL = nprioL;
        end else begin
          ret = tagged Valid ({1, iR});
          prioR = nprioR;
        end
      end else begin
        thisPrio[0] = False;
        ret = tagged Valid ({0, iL});
        prioL = nprioL;
      end
    end else if (idxR matches tagged Valid .iR) begin
      thisPrio[0] = True;
      ret = tagged Valid ({1, iR});
      prioR = nprioR;
    end

    return tuple2(ret, append(thisPrio, append(prioL, prioR)));
  endfunction
endinstance

