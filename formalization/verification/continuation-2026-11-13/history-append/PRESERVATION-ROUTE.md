# Source-first route to frozen successful-reference preservation

No native calibration enters internal derivations. Frozen final target has only
successful Option lookup as validity premise, arbitrary source terms.

1. Course-of-values table equations: checked. TableLookupZero and TableLookupGap
   candidates prove lookup(gap,table(base+gap,right)) = SOME(head(table(base,right))).
2. Normalize actual value AST: inputCode=succ n; inputHead/head and inputTail/tail;
   index=actual difference(tail(succ n),n); reference=actual lookup(index,table n);
   recursiveResult=pred(reference); result=actual cons(head,recursiveResult).
3. For actual cons(a,b), existing PairSecondBound supplies b≤pair(a,b). Eliminate
   its existential gap using internal difference cancellation + TableLookupGap.
   Head/tail inverse and cons-copy agreement yield exact InternalAppendCons.
4. To cover arbitrary positive codes without assuming unpair reconstruction,
   prove the checked right decoder output is ≤ its input from its bounded-scan
   range invariant. Inner steps return previous or enumerated second coordinate;
   every enumerated second coordinate at complete scan is ≤code. Outer scan
   preserves that bound from seed0. Thus tail(succ n)≤n internally.
5. The same table argument then yields unrestricted positive-code recurrence:
   append(succ n,right)=cons(head(succ n),append(tail(succ n),right)).
   This does NOT require succ n = cons(head(succ n),tail(succ n)).
6. Derive general drop shift drop(succ index,code)=drop(index,tail(code)) by PA
   iteration induction, and reference(succ n)=SOME(head(succ n)) by actual select.
7. Index induction with universally quantified code/entry proves preservation:
   zero-history premise contradicts successor-not-zero; positive histories use
   the unrestricted append recurrence and lookup shift. IH is instantiated at
   actual tail(code), not assumed for a fixed unchanged history.

Remaining engineering: arbitrary installed lookup/head/tail copies need actual
internal transport where syntax is duplicated; use exact source equations or
prove same-Program copy congruence, not native equivalence. Existing pair-copy
agreement is already internally checked.
