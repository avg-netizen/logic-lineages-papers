# Natural-input elementary normalization

## Current scope

Target-only preflight passed before proof authoring. The exact checked target
is: for every n and set S of Fin n natural valuations, Dioph S iff S is represented
by a finite elementary system with finite natural existential witnesses.
Original free parameters retain their identity and all values may be zero.
All three exact aliases passed the bounded native gate and standard-axiom
audit. The six-file package has a 20-module current-source verified closure.
See `ELEMENTARY-ACCEPTANCE.json`.

The only RHS forms are a natural constant, existential wire, original parameter,
addition of two wires, or multiplication of two wires. Each constraint equates
one existential output wire with a RHS. No polynomial or general expression
is hidden inside an elementary constraint.

## Construction

1. IsPoly induction splits an integer-polynomial value into the difference of
   two actual natural arithmetic expressions. Subtraction crosses the two
   sides; multiplication uses the ordinary four-term signed product identity.
2. The finite union of both expressions' subterms supplies auxiliary wires.
   Each node has its literal elementary equation; one more equation equates
   the roots. Actual evaluation gives canonical witnesses. Structural induction
   proves every satisfying assignment computes the same expression values.
3. Finite witness and equation types are transported to explicit Fin blocks.
4. The already checked finite-witness extraction for Dioph supplies an integer
   polynomial on the original parameters plus finitely many original witnesses.
   Those witnesses are moved to a separate auxiliary-wire summand. The original
   free parameters are unchanged. No PosNat compiler is used.
5. Conversely each elementary equation is Diophantine; fixed finite conjunction
   and finite existential projection prove soundness of every resulting system.

This proves existential semantic normalization. It does not assert a computable
algorithm extracting a circuit from an arbitrary extensional Dioph/IsPoly proof,
and it does not assert the source's numerical 7/8 size bounds.

## Primary-source correspondence

https://github.com/uds-psl/H10-LMCS-v1.1/blob/c2586aee45cf60e7fb8b112ac701b02d7dc3cfeb/theories/H10/Dio/dio_elem.v

- Lines 142–196: the five natural RHS forms and elementary constraints.
- Lines 564–567: finite elementary normalization preserving every original
  natural parameter valuation. Its numeric bounds are not claimed here.

The local implementation is an alternative exact semantic construction via
finite subterm wires. It imports no Coq theorem or extra axiom.

## Remaining boundary

Variable-length witness-row packing, full variable bounded-universal closure,
ordinary recursion/minimization graph cases, universal evaluation, computable
polynomial specialization, RE reductions and genuine MRDP remain pending.
A fixed finite conjunction here is not variable bounded-universal closure.
