// Adapted from https://github.com/mtikekar/advanced_bsv
import FIFOF :: *;
import SpecialFIFOs :: *;
import Vector :: *;
import GetPut :: *;

interface SearchTree#(numeric type n, type key_t, type val_t);
  interface Vector#(n, Put#(val_t)) iport;
  method Action deq;
  method val_t first;
  method Bool notEmpty;
  method Bool search(key_t k);
endinterface

typeclass Searcher#(numeric type n, type key_t, type val_t);
  module mkSearchTree#(function Bool f(key_t k, val_t v))
    (SearchTree#(n, key_t, val_t));
endtypeclass

instance Searcher#(1, key_t, val_t) provisos (Bits#(val_t, tSz));
  // Base instance of 1-long vector
  module mkSearchTree#(function Bool f(key_t k, val_t v))
    (SearchTree#(1, key_t, val_t));
    FIFOF#(val_t) in <- mkBypassFIFOF;
    Vector#(1, Put#(val_t)) i;

    i[0] =
      (interface Put;
        method put = in.enq;
      endinterface);

    interface iport = i;
    method deq = in.deq;
    method first = in.first;
    method notEmpty = in.notEmpty;
    method search(k) = in.notEmpty ? f(k, in.first) : False;
  endmodule
endinstance

instance Searcher#(n, key_t, val_t) provisos (
  Div#(n, 2, hn), Add#(hn, hm, n),
  Searcher#(hn, key_t, val_t), Searcher#(hm, key_t, val_t),
  Bits#(val_t, tSz)
);

  // General case
  module mkSearchTree#(function Bool f(key_t k, val_t v))
    (SearchTree#(n, key_t, val_t));
    // two subtrees
    SearchTree#(hn, key_t, val_t) l <- mkSearchTree(f);
    SearchTree#(hm, key_t, val_t) r <- mkSearchTree(f);
    Reg#(Bool) lPrio <- mkReg (True); // the left tree has priority
    FIFOF#(val_t) out <- mkBypassFIFOF;

    (* fire_when_enabled *)
    rule arbitrate_both(l.notEmpty && r.notEmpty);
      let x = lPrio ? l.first : r.first;
      out.enq(x);
      if (lPrio) l.deq; else r.deq;
      lPrio <= !lPrio;
    endrule

    (* fire_when_enabled *)
    rule arbitrate_left(l.notEmpty && !r.notEmpty);
      let x = l.first;
      out.enq(x);
      l.deq;
      lPrio <= False;
    endrule

    (* fire_when_enabled *)
    rule arbitrate_right(!l.notEmpty && r.notEmpty);
      let x = r.first;
      out.enq(x);
      r.deq;
      lPrio <= True;
    endrule

    interface iport = append(l.iport, r.iport);
    method deq = out.deq;
    method first = out.first;
    method notEmpty = out.notEmpty;
    method search(k) = begin
      let searchL = l.search(k);
      let searchR = r.search(k);
      let searchO = out.notEmpty ? f(k, out.first) : False;
      searchL || searchR || searchO;
    end;
  endmodule
endinstance

