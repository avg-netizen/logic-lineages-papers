# Paper 16: selected symbolic J fold with actual empty base

[ordinals.tex](../../../16-persistent-marking-termination-ordering/sections/ordinals.tex)
149–153 uses the finite multiset argument on the actual adopted carrier.
[This thin wrapper](../../LogicLineages/PersistentMarking/NumberedWindowInternalLiteralSparseJFoldWithEmptyProof.lean)
combines #1597's checked original symbolic packed J fold with #1596's
actual unconditional J(empty) in exactly the same installed `literalData
i r` source body. The assumed exact parse, typed scratch and first-order
scalar I derivations of all actually read members are untouched. The
caller no longer supplies the empty J derivation. Actual same-body scalar
to singleton J promotion and the original certified origin split remain
explicit premises. No checker substitution or unconditional J or numbered
closure is claimed. One exact native audit is requested.
