module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableRegionsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn z suc sucRelabel zRelabel)
open InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open InternalSquareRootArithmeticSupportProof (orderLeft orderRight)
open InternalOriginalPairingOrderArithmeticProof (withHyp)
open InternalQuotientComparisonProof InternalPositiveUnfoldingSupportProof
open InternalBetaTotalityProof (disjunctionElimination)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem compareCases (x y : InternalGraphComposition.OTerm alpha) (psi : Formula alpha)
    (hl : Nonempty (Derivation body (ltF x y :: Delta) psi))
    (he : Nonempty (Derivation body (eqn x y :: Delta) psi))
    (hg : Nonempty (Derivation body (ltF y x :: Delta) psi)) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨hc⟩ := actualOriginalComparison body alpha x y
  have hv := compareView (weakenClosed hc Delta)
  obtain ⟨hl⟩ := hl
  obtain ⟨he⟩ := he
  obtain ⟨hg⟩ := hg
  have hrest : Derivation body Delta (((eqn x y) ⊔ ltF y x).imp psi) :=
    Derivation.implicationIntroduction (disjunctionElimination
      (Derivation.hypothesis List.mem_cons_self)
      (InternalBetaTotalityProof.addHyp (Derivation.implicationIntroduction he) _)
      (InternalBetaTotalityProof.addHyp (Derivation.implicationIntroduction hg) _))
  exact ⟨disjunctionElimination hv (Derivation.implicationIntroduction hl) hrest⟩

/-- A strict lower bound supplies a real symbolic predecessor witness. -/
theorem positiveCases (lower x : InternalGraphComposition.OTerm alpha) (psi : Formula alpha)
    (hp : Nonempty (Derivation body Delta (ltF lower x)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (y : InternalGraphComposition.OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (eqn (x.relabel j) (suc y))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply zeroSuccessorCases Delta x psi
  · obtain ⟨h⟩ := withHyp hp (eqn x z)
    have hz := orderRight lower (Derivation.hypothesis List.mem_cons_self) h
    obtain ⟨hn⟩ := InternalApplicationValidityStackAppendTransitionProof.notLessZero
      (body := body) (Gamma := eqn x z :: Delta) lower
    exact ⟨Derivation.explosion (Derivation.implicationElimination hn hz)⟩
  · exact next

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableArithmeticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableArithmeticProof
