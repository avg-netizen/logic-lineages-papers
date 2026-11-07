module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalListCodec InternalListCodecSupportProof InternalControlGraphSupportProof
open InternalRecursionClosureProof InternalTagArithmeticSyntaxProof

/-- These derivations depend only on the original graph calculus and its proved
syntactic arithmetic suppliers, not the separate evaluation calibration. -/
theorem actualOriginalConsIntroduction : InternalListCodecTargets.ActualOriginalConsIntroduction := by
  intro body α p h t
  obtain ⟨d⟩ := consValue (body := body) (Gamma := [pairGraph p h t]) p h t
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

theorem actualOriginalConsDestruction : InternalListCodecTargets.ActualOriginalConsDestruction := by
  intro body α n h t
  obtain ⟨d⟩ := consDestruction (body := body) (Gamma := [consGraph n h t]) n h t
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [equalEqn] using (show Nonempty (Derivation body []
    ((consGraph n h t).imp ((unaryGraph headCode h n) ⊓
      ((unaryGraph tailCode t n) ⊓ (eqn n z).not)))) from
    ⟨Derivation.implicationIntroduction d⟩)

theorem actualOriginalConsDestructorEquations : InternalListCodecTargets.ActualOriginalConsDestructorEquations := by
  intro body α n h t a b
  let A := (consGraph n h t) ⊓ ((unaryGraph headCode a n) ⊓ (unaryGraph tailCode b n))
  have hc : Nonempty (Derivation body [A] (consGraph n h t)) :=
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
  obtain ⟨d⟩ := consDestruction n h t hc
  obtain ⟨hh⟩ := valueUnique headCode a h (Fin.cons n Fin.elim0)
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionLeft d⟩
  obtain ⟨ht⟩ := valueUnique tailCode b t (Fin.cons n Fin.elim0)
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight d)⟩
  simpa only [equalEqn] using (show Nonempty (Derivation body [] (A.imp ((eqn a h) ⊓ (eqn b t)))) from
    ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction hh ht)⟩)

theorem actualOriginalConsInjectivity : InternalListCodecTargets.ActualOriginalConsInjectivity := by
  intro body α n h t h' t'
  let A := (consGraph n h t) ⊓ (consGraph n h' t')
  have hc : Nonempty (Derivation body [A] (consGraph n h t)) :=
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
  have hc' : Nonempty (Derivation body [A] (consGraph n h' t')) :=
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  obtain ⟨d⟩ := consDestruction n h t hc
  obtain ⟨d'⟩ := consDestruction n h' t' hc'
  obtain ⟨hh⟩ := valueUnique headCode h h' (Fin.cons n Fin.elim0)
    ⟨Derivation.conjunctionLeft d⟩ ⟨Derivation.conjunctionLeft d'⟩
  obtain ⟨ht⟩ := valueUnique tailCode t t' (Fin.cons n Fin.elim0)
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight d)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight d')⟩
  simpa only [equalEqn] using (show Nonempty (Derivation body [] (A.imp ((eqn h h') ⊓ (eqn t t')))) from
    ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction hh ht)⟩)

theorem actualOriginalNilTestGraph : InternalListCodecTargets.ActualOriginalNilTestGraph :=
  InternalControlGraphProof.actualOriginalZeroTestGraph

theorem actualOriginalListCodecTotalFunctional : InternalListCodecTargets.ActualOriginalListCodecTotalFunctional :=
  fun body => ⟨actualOriginalPrograms body 2 consCode,
    actualOriginalPrograms body 1 headCode, actualOriginalPrograms body 1 tailCode,
    actualOriginalPrograms body 1 nilTest⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecProof
