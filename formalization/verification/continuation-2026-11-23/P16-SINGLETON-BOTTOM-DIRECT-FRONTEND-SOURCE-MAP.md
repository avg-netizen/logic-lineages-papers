# Paper 16: singleton-bottom direct front end

Source: `16-persistent-marking-termination-ordering/sections/ordinals.tex`
lines 52–58 (whole bottom), 74–76 (positive quotient paths), 84–98
(tagged I/J and strict finite multiset replacement), and 142–153
(the multiset part of arithmetic accessibility).

This first packet recognizes a single physical bottom-address field at the
actual raw code, using exact one-cell arity and the same original address
bottom recognizer. The all-input numerical value-one characterization
covers malformed codes. The checked open introduction uses the literal
packed singleton with arbitrary object context/type fields. It follows
from the genuine cons, exact packed arity, and original bottom recognizer
graphs, not from the numerical characterization.

For any supplied original direct certificate from a singleton bottom,
nonempty removal and source permutation leave no retained occurrence
and force the removed list to contain exactly that bottom. An inserted
occurrence would carry an impossible positive path from actual bottom.
The target list is therefore empty, whose actual numeric code is zero.
This is a numeric semantic guard for a later new branch-visible dSB.
No dSB is installed here, no previous selected body is changed, and
no open proof of target-zero from an arbitrary prior d is asserted.
No singleton-free deletion claim or full internal multiset closure.

Native candidate (pending):
`LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomChecks`.
Exact authored source SHA-256:
- c75a46f3713c87a89c61cd2bd853f0a1bfb39fbe6e62983b45eb167688762ee2  LogicLineages/PersistentMarking/NumberedWindowInternalSingletonBottomChecks.lean
- 4a5d9cf38cd0dfff8cdd8569723ba5b05e7faf0d8128c573e9d13cbeb11b9ca6  LogicLineages/PersistentMarking/NumberedWindowInternalSingletonBottomProof.lean
- 43128ca9dda004f053189d43a366792357cb3411e87163419f6d0a501f4ef9a4  LogicLineages/PersistentMarking/NumberedWindowInternalSingletonBottomTargets.lean
