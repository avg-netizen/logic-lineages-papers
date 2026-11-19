# Paper19 lem:affine-head: current selected-policy and current-control head fields

Numbered source: `sections/realization.tex` 27–55; actual tracked grammar,
shared names/units and real scalar annotations in lines 1–26.
The setting's generated positive-coordinate invariant appears in
`sections/setting.tex` 131–143.

* The manuscript fixes the name F whose partial is being taken. The exact
  typed source context is `Ty.curriedGround (k+1) :: Γ`: the designated
  F is the head so the actual existing `AdmissiblePartial.run p 1` deletes
  precisely F. Every other ambient name and its original type stays in Γ.
  This is a choice of context order for the distinguished name, not an
  additional restriction on named syntax or a bound on binder depth.
  The direct actual `TrackedSource.Generated` grammar includes F,
  ground variables, literal F-free blocks of curried level at most one
  (arbitrary internal typed T, captured ground), ground application and
  arbitrary nesting of ground lambdas, including functional-result bodies.
  `TrackedSource.Proof.exactGrammar` connects every such actual t to erasure.
* Both the literal head tree and scalar support use actual selected p
  source assignments, not arbitrary assumed head/tree certificates.
  Every positive result field is covered (hence in particular the first).
  Every selected actual scalar collapse carries both its actual head h and
  its own tail t; even if two occurrences have syntactically identical h,
  one tail's activity cannot witness the other. `SelectedCollapse` traverses
  the real scalar copy/active sum/collapse tail relation and never descends
  into positive fields. Active head implies this actual tail is active.
* `HeadConclusion` fixes the actual policy's partial `run p 1 h` and
  both original positive indices. At the actual shared/common unit
  valuation, its first output is the actual h plus literal finite
  `HeadFiniteSurplus.surplus h`; ordinal plus on a finite right operand
  is the stated operation. The finite surplus is zero iff the actual
  bare tracked head F1, and nonfinite (at least omega) implies positive
  surplus. Output two is the exact finite `secondCount h`, itself positive.
  Both actual generated partial grade witnesses are required, not assumed.
* There is a genuine current-control bridge rather than an interpreter
  alias: `PositiveNoCollapse` must prove that an actual positive
  `GeneratedOrdinalGrade` expression contains no collapse anywhere and that
  `ParametricSourceSuccessor.denoteWith f` equals ordinary `denote` there.
  The collapse constructor is grade zero; positive add/graded ExpProd
  keep all children positive. The actual head and each positive partial
  output must separately satisfy that grade condition before reusing the
  preserved p-parametric `HeadFiniteSurplus.Proof` evaluation.
* The current `commonUnits` (ground natural-wire +1, every functional
  coordinate one) is explicitly calibrated against the old genuine
  `UnitObservation.substitution` valuation in `SameCommonUnits` using
  its verified actual closed finite and functional values. This is a
  shared observation, not a source all-one inhabitant or a special choice
  of parsing policy/control. No particular f (including Phi or gamma)
  is required: the structural grade proof explains why f is irrelevant
  only on these positive fields, not their containing scalar assignment.

No scalar accounting, carrier-coefficient reserve, or whole decision
procedure is asserted. Preserve existing frozen/accepted and historical
files; these are add-only comparator modules. Independent source scope,
target-only preflight, authored source review and full current recursive
native evidence are separate.
