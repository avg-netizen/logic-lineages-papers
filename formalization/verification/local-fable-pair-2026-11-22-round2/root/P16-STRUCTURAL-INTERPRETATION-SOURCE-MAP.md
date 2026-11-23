# Paper 16 `lem:structural-interpretation`: comparator for the corrected statement

Printed lemma (`sections/decision.tex`, l.149–155): interpretation and the original-spine helper are
monotone and commute with weakening; interpretation respects capture-avoiding substitution; for
environments interpreting concrete substitutions the helper interprets full application of the
substituted source, including its undefined cases.

`paper16/recovery-nov19/MANUSCRIPT-CORRECTION-HANDOFF.md` records that the full-application clause is
false as printed: accepted #396 (`AvailabilityGap`) is a counterexample at the bottom retained family,
and #398 proves the clause at a fixed point of the checked operator. The manuscript has not been edited.

Frozen `LogicLineages/PersistentMarking/StructuralInterpretationCorrectedTargets.lean`
(sha256 `8ef7ed77aafc53e8ccfb0a1537ec98945a62c4da8bf4f55ffa0af6c2a3225a72`):
- `CorrectedStructuralInterpretation` := `InterpretationLaws` (#394) ∧ `FreeSubstitution` (#396) ∧
  `BoundSubstitution` (#397) ∧ `FixedApplication` (#398).
- `CorrectedWithBoundary` := that ∧ `AvailabilityGap` (#396).
Proved by conjunction of the accepted theorems (legacy core modules, core profile gate).

This does **not** promote the numbered lemma. It becomes the lemma's comparator only if the owner
applies the fixed-point qualification to the manuscript. The handoff also flags decision.tex 228–230
(the adequacy proof's use of this lemma inside a stage induction); accepted #413–#416 avoid that site.
Whether `FreeSubstitution` ∧ `BoundSubstitution` together are what the paper means by
"capture-avoiding substitution" was not re-examined here.
