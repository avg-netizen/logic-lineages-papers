# Paper 16: actual numeric recursive lambda validity and measure provenance

Frozen exact targets and initial proof, native gate pending. Start from
the actual original sparse unpackNode raw = some (2,[ty,q]), not a
predicted shape. Literal earlier-index bound from physical original
codec gives q < raw. For the actual original forward syntax table, prove
lookup at any earlier index i is precisely syntaxBits i by the real
append recurrence (not the default row). The original termParts tag-2
clause now gives exact syntax-bit equivalence to the real annotation type
bit and the actual body's own syntax bit.

Independently in the same raw branch, the actual bounds recurrence reads
the body's original earlier measure row, with source tag-2 formula
(childDepth+1,childWidth). The calibrated selected V/M corollary uses
one V and one M for both original codes and only the repository's precise
TermSyntaxCalibrated and TermMeasureCalibrated predicates. It returns
actual native evaluations and their original encodings; it derives these
from the earlier-row facts, not from stipulated parent/body values. It
can be specialized to the independently calibrated reselected V-prime,
but gives no actual open report or graph transfer for unchanged V or M.
In particular the open lambda own-cover theorem still needs genuine
derived child typing/measurement and paired report suppliers.

Printed Decision context (decision.tex 8-37, 45-60, and adequacy):
* Ordinary inputs s,t are fixed. K is the subtype closure of their
  literal types; V is their free-name set, not the syntax Program V.
* B bounds lambda nesting in the fixed target t. A finite context Γ
  assigns types from K to used fresh typed port slots. Extension adds
  only unused slots and never retypes old ones. Opening a target lambda
  consumes exactly one such unused port and descends one observation.
* Retained observations are only opened subterms of that same t, at
  the appropriate type σ, with externally bound variables assigned
  to suitable typed ports and remaining depth at most B-|Γ|.
* Recursive source heads must stay among heads of s; Copy's introduced
  target head does not become a fresh recursive source. Free source
  names are confined to V plus used Γ. Capture-avoiding substitution
  preserves annotations/node types and does not create an extra
  observation context; FAbs alone opens the typed target port.
* These invariants are hypotheses/closure conclusions at the printed
  comparison presentation with coherent weakening and full tuple
  operations, not consequences of raw syntax validity. This packet
  proves neither their realization by the sparse cover program nor
  the printed fixed-point adequacy/stage-soundness.

Static local closure sizes (root included): NumberedWindowInternalCoverLambdaProvenanceTargets 882, NumberedWindowInternalCoverLambdaProvenanceProof 886. No explicit Mathlib.Logic.Hydra or Mathlib.Tactic.Linarith in these closures.

| Source | SHA-256 |
| --- | --- |
| formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverLambdaProvenanceTargets.lean | bac61440458d882aed42024bcb8f4f796c71b1d6cd653159714476f1a9adb253 |
| formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverLambdaProvenanceProof.lean | 1a19eeda5315af9aabc084485243da80ef2df098d4e8e6c4b8da70ff4ca7743a |
| formalization/LogicLineages/PersistentMarking/NumberedWindowSyntaxAlgorithm.lean | 372235cb3dadc4d33c724728e1da43fb0752e5eb995d47c9dae75f1127593b52 |
| formalization/LogicLineages/PersistentMarking/NumberedWindowCoverBoundsAlgorithm.lean | 2fd441cf84517c14c06f9414cf6cc8302dab24618c2523e2ac6cf61037edb384 |
| formalization/LogicLineages/PersistentMarking/NumberedWindowFieldAlgorithm.lean | 4b44f21f2bbaa6695a65ae0e34afb20b0bad3facf2693f1f7018d633488ba7b4 |
| formalization/LogicLineages/PersistentMarking/NumberedWindowRawExchangeVerticesBoundsTableProof.lean | 9d6138c3943f0ab9f57e44dc867c19681891a8b554b3440a3d25c257e91c516f |
| formalization/LogicLineages/PersistentMarking/NumberedWindowRawExchangeVerticesCodecProof.lean | 74239b5668344c85aad461ddd0f73372c44a4a983f0383a0ee74d02468d38caf |
| formalization/LogicLineages/PersistentMarking/NumberedWindowInternalFactoredCoverTargets.lean | cb0c2b44be27461354b80a72eeb104d17c005bef45923fd96bcdbc2593f2fd31 |
| formalization/LogicLineages/PersistentMarking/NumberedWindowInternalAuxExchangeMemoStepTargets.lean | e5f339e51fa6ba9f8cce62ce27f727ab4ddb88bf7a984ae867e4e2b06680b7c8 |
| 16-persistent-marking-termination-ordering/sections/decision.tex | 2dcac539d8d6466fa8baa87f88cc3841f17c64e4481bd860bb6f67690eada275 |
