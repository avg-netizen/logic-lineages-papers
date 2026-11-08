# Checked: parameterized bounded descent

All **six unchanged frozen targets** passed exact aliases and actual axiom
checks on the first proof-check attempt. The exact gate is
`build-reports/1794153203210562738-6.json`. All **65 own declarations**, including
the six aliases, were audited; only `propext`, `Classical.choice` and
`Quot.sound` occur. No frozen specification or original supplier was changed.

For arbitrary binary ASTs R and V with inputs [value, parameter], the actual
transition accepts R(value,parameter) precisely when it strictly decreases
the value, has V-output exactly one at the same parameter, and has the same
original value left tag. Otherwise it returns the original value. The actual
normalizer uses parameter-carrying iteration at [value+1,value,parameter].

The original calculus proves that the result is at most the input value,
is fixed by the actual transition at the same parameter, preserves exact-one
validity when present, and preserves the original value type tag. Strong
internal stabilization holds whenever value is at most fuel. Its zero-fuel
case includes every nonzero parameter: the carried pair need not be zero.
The parameter is never used as the type tag or included in the descent measure.

The proof uses original full-language natural induction with a four-variable
universal row [input,out,typ,parameter]. The actual parameterized front-successor
and fixed-point rules, original graph composition and equality transport,
and the strict first-step split keep the identical parameter throughout.
It does not use external evaluation calibration as an internal proof,
specialize a unary program after receiving a symbolic parameter, introduce
assumptions on the binary leaves, or apply unary descent to the whole pair.

The focused proof/preflight closure has **1,087 current-source-matched local
modules** across **23 immutable native receipts**. All **1,072 broader frozen
Lean inputs** have matching successful module rows, and all **1,080 frozen/
prerequisite pins** are unchanged. Existing successful supplier rows remain
valid when a later module in the same supplier run failed. Both new checker
runs passed completely. No current component warnings occur.

Peak successful component RSS was **1,062,748 KiB**, below the unchanged
1,536 MiB cap. The sole compiler slot was **released at
2026-11-08T15:53:49.677142+00:00** after both native sessions completed and both
shared locks were verified free. No further compiler run is scheduled.

The frozen specification, static checks and source correspondence retain the
pre-proof chronology. Their pending-status descriptions are historical;
this file and `ACCEPTANCE.json` record the later checked result without
changing any frozen bytes. Independent postproof review and coordinator
adoption remain pending.

This is a supporting component only. Source-specific identification with the
original least-code representative, uniform canonical selection, uniform
fold/path correctness, unconditional `CertifiedApplicationLift`, the remaining
constructor/lambda/substitution arguments, and all-term accessibility are not
proved here. No numbered source promotion, Git action, full-root build, or
remote CI is claimed.
