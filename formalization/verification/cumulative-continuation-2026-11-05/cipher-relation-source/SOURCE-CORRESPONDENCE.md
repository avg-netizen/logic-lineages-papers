# Cipher relations for bounded-universal assembly

## Current scope

Target-only preflight passed before proof authoring. All eight exact aliases
passed the bounded native gate and standard-axiom audit: constant and
multiplication arithmetic calibration, addition/multiplication pointwise
specifications, and genuine Diophantine graphs of Code, Const, source Code_plus
and source Code_mult. The five-file package has a 36-module current-source
verified closure. See `CIPHER-RELATION-ACCEPTANCE.json`.

This is the relation layer used by the source's elementary-constraint packing.
It is not variable bounded-universal closure or MRDP.

## Source domains and empty cases

- Code n q a means an actual bounded sparse vector exists with code a.
- Const n q c a requires every entry to be c. When n=0, this means only 1<q and
  a=0; c is unrestricted. The exact bound is n=0 OR c<2^q.
- Add a b c is a=b+c. Its definition has no validity guard. The pointwise
  addition theorem takes three separate IsCipherOf hypotheses.
- Mult retains the source's literal auxiliary witnesses and empty disjunction.
  At n=0 it is TRUE for every q,a,b,c, including q=0 and invalid codes. Its
  pointwise multiplication theorem separately assumes three valid codes.

The eliminated MultEquations is proved equivalent to that literal relation;
no global n+1<q condition or code validity was silently added.

## Primary source

Pinned commit c2586aee45cf60e7fb8b112ac701b02d7dc3cfeb:
https://github.com/uds-psl/H10-LMCS-v1.1/blob/c2586aee45cf60e7fb8b112ac701b02d7dc3cfeb/theories/H10/Matija/cipher.v

- Actual encoding: 1215–1218; Code: 1296–1299.
- Const: 1323–1327.
- Code_plus/specification: 1361–1369.
- Code_mult/specification: 1498–1514.

The proof uses checked sparse sums, validity, addition, masked multiplication,
actual all-ones graph and natural AND graph. The Diophantine closure steps use
only ordinary arithmetic, powers, finite conjunction/disjunction and finite
existential projection. No unproved variable-universal premise is introduced.

## Next genuine gap

Source dio_elem.v normalizes to five natural RHS forms: constant, existential
variable, free parameter, addition, multiplication. Its elementary-system
normalization for all original natural inputs is not yet local. Positive-input
PolynomialCircuit and exponential-gadget CircuitReduction cannot be silently
substituted for this theorem. A possible direct construction represents an
integer polynomial as two natural expression trees and assigns finite fresh
wires to all subterms, retaining zeros and all original free inputs.

Source dio_bounded.v then compiles six cases (separating the index parameter),
imposes CodeNat on the index row and Code on each fixed witness row, and proves
variable-length packing by choosing one common q for a finite witness family.
That packing equivalence, elementary normalization, ordinary recursion and
minimization, universal evaluation and effective polynomial specialization
remain pending.
