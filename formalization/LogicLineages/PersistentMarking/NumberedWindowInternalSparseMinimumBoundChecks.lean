module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open NumberedWindowInternalSparseOrderedMinimum (scratchMinimum)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseMinimumBoundTargets
open NumberedWindowInternalSparseMinimumBoundWitnessProof (casesValue transportBound)

theorem exact_OpenMemberHasBoundedMinimum : ExactOpenMemberHasBoundedMinimum :=
  NumberedWindowInternalSparseMinimumBoundInductionProof.memberHasBound

theorem exact_OpenScratchMinimumLowerBound : ExactOpenScratchMinimumLowerBound := by
  intro body α Γ code candidate minimum
  let A := unary scratchMinimum (suc minimum) code ⊓ memberGraph code candidate
  let Δ := A :: Γ
  have input : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨memberRule⟩ := exact_OpenMemberHasBoundedMinimum body α Δ code candidate
  have witness := Derivation.implicationElimination memberRule (Derivation.conjunctionRight input)
  have bound : Nonempty (Derivation body Δ (ltF candidate minimum).not) := by
    apply casesValue code candidate _ ⟨witness⟩
    intro β j Θ found keep ⟨row⟩
    have original := renameInto ⟨Derivation.conjunctionLeft input⟩ j Θ keep
    rw [unaryRename,sucRelabel] at original
    have same := valueUnique scratchMinimum (suc found) (suc (minimum.relabel j)) ![code.relabel j]
      ⟨Derivation.conjunctionLeft row⟩ original
    obtain ⟨e⟩ := same
    change Nonempty (Derivation body Θ ((ltF candidate minimum).relabel j).not)
    rw [orderRename]
    exact transportBound _ found _ (cancelSuc e) (Derivation.conjunctionRight row)
  obtain ⟨bound⟩ := bound
  exact ⟨Derivation.implicationIntroduction bound⟩

#print axioms exact_OpenMemberHasBoundedMinimum
#print axioms exact_OpenScratchMinimumLowerBound
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundChecks
