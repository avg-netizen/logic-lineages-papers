# Paper 16: numeric calibration of exact per-cell-parameterized positive walk

The exact original checker has a syntactic parameter `A : Program 4` only
for its physical per-cell update. The actual parser, sparse ordered
certificate, nonempty check and result comparison remain in the original
program. The module `NumberedWindowInternalParameterizedPositiveFold`
has checked its definitional original instance
`positiveAt (advance raw L) = positive raw L`
(receipt 1795459046297684160-32); this packet does not change that file or
replace its program with an alternative parser.

* **State:** direct physical evaluator A at the original ordered fields:
  packed context, type, optional current code, and actual chosen cell head.
  The scratch update installs the real cell tail and exact A result.
* **Iteration:** the actual scratch loop holds a zero cursor, rejects a
  malformed positive cell by the original dead state, and otherwise
  executes A on its chosen physical head and advances to its true tail.
* **Fuel:** genuine strong induction on original packed certificate numbers.
  The original `unpack` equations and original sparse-tail bound identify
  the completed scratch result with `foldPhysical A` over that exact
  decoded list in order. Malformed certificates are absent; an empty list
  retains the actual optional start. State 0 is fed as an actual numerical
  input to A on each real later cell; no annihilation law on arbitrary A
  is assumed.
* **Result:** certificate-as-fuel, real final state extraction, and the
  literal nonempty-and-equals test. The checker evaluates to 1 exactly
  when the certificate is nonempty and its actual decoded A-fold returns
  the real target, otherwise 0. In particular `unpack 0 = some []` never
  makes the positive checker accept an empty certificate.

No object-theory reflection, zero-rank invariant or replacement of the
real physical program is supplied by this numeric result. A separate
specialization can use the same checked numeric statement with the literal
`zeroOutput` program and the actual zero-rank prefix/path invariants.
