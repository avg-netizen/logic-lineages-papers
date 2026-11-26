module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionRejectGapProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseFieldInductionTargets (someCons malformed)
open NumberedWindowInternalSparsePositiveFold (finish)
open NumberedWindowInternalSparsePositiveOutputTargets (args4)
open NumberedWindowInternalSparsePositiveDeadCurrentChecks (exact_OpenMalformedFinishZero)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets

attribute [local irreducible] programGraph finish

theorem properCell {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least : Program 3) (ctx ty source cert target : OTerm α)
    (good : Nonempty (Derivation body Γ (finishedNonempty raw least ctx ty source cert target))) :
    Nonempty (Derivation body Γ (someCons cert)) := by
  obtain ⟨d⟩ := good
  let p := someCons cert
  have no : Nonempty (Derivation body (p.not :: Γ) p) := by
    have bad : Nonempty (Derivation body (p.not :: Γ) (malformed cert)) :=
      ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft (addHyp d p.not))
        (Derivation.hypothesis List.mem_cons_self)⟩
    have zero := closedApply (exact_OpenMalformedFinishZero body raw least α ctx ty (suc source) cert) bad
    obtain ⟨eq⟩ := valueUnique (finish raw least) (suc target) z (args4 ctx ty (suc source) cert)
      ⟨Derivation.conjunctionRight (addHyp d p.not)⟩ zero
    exact ⟨Derivation.explosion (sucNeZeroApply eq)⟩
  obtain ⟨n⟩ := no
  exact ⟨disjunctionElimination (excludedMiddle p)
    (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))
    (Derivation.implicationIntroduction n)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionRejectGapProof
