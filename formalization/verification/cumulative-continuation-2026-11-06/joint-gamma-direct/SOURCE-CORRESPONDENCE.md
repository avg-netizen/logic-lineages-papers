# Joint-context direct multiset certificate checking

Baseline: `5cf0f5badecbcfdf7311057ab64d48de5a2dc8b8`, preserving the accepted
joint-context original quotient-edge/path component and all earlier sources.
Paper06 `paper.tex` lines 563–569 uses the arithmetic relation DM(R), direct
multiset replacement over R, in the second tagged positive operator. This
component lifts the original certificate-checking computations jointly in Gamma.
It does not establish ID1 derivability, accessibility, well-foundedness, the
whole `lem:id1`, or any private II5 conclusion.

The three targets name ORIGINAL `QuotientDominationCertificates.test`,
`QuotientDirectCertificates.directTest`, and `numericTest` directly. Only the
finite signature size and arity are fixed. Gamma, symbol/type windows,
precedence table, source/target lists or numbers, and certificates are inputs.
The domination checker retains one certificate per inserted occurrence, permits
reuse of removed indices, rejects missing/extra entries and out-of-range
indices, and checks the original positive-path certificates. The direct test
retains both original list permutation tests and a nonempty removed list.
The numeric test uses the original Encodable decoders, rejecting malformed
source, target and certificate codes without a validity premise.

Accepted `QuotientDirectPrimrecTargets` fixes Gamma outside Primrec. The new
joint-context original positive-path checker is the missing supplier. The
Nov 4 R005 direct-fold/primitive draft is archived as unaccepted, not an
accepted supplier. Its finite fold structure is reused transparently, now
with the ORIGINAL positive-path and direct-multiset checkers throughout.
All archived files, prior targets and source definitions remain unchanged.

The helper fold and exact target types are frozen before proof creation.
Acceptance requires a successful comparator preflight, exact target aliases,
and transitive axiom closures within propext, Classical.choice and Quot.sound.
Only the unchanged serialized bounded checker may launch native proof checks.
No manuscript, global register, checker, dependency, root import or CI changes.
No full encoded context-object Program presentation is claimed.
