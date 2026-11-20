module
public import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTransitivityTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityAddressProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityBinderProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTransitivityAddressProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeSyntaxProof (unaryRename)
open NumberedWindowInternalAtomicRefinement (atSource atTarget)
open NumberedWindowInternalPositiveEndpointRefinement (withEndpointCarriers)
open NumberedWindowInternalPositiveEndpointRefinementObjectChecks (exact_OpenPositiveEndpointCarrierGraphs)
open NumberedWindowInternalSparseAddressTransitivityAddressProof (combine)
open NumberedWindowInternalSparseAddressTransitivityBinderProof (consume provide suppliedEdgeRename)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalMatchReductionTargets (suppliedEdge)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalPositiveEndpointRefinementTransitivityTargets

private theorem acceptsGraph {α : Type} (r : Program 3) (x w y : OTerm α) :
    accepts r x w y = programGraph r (suc z) ![x,w,y] := rfl

private theorem wrapperAST (i : Program 1) (r : Program 3) :
    withEndpointCarriers i r = conjunction r (conjunction (atSource i) (atTarget i)) := by
  simp only [withEndpointCarriers,exact_DispatchControlAST.2.2.2.2.2]

section
attribute [local irreducible] programGraph

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem writeSlot (i : Program 1) (k : Fin 3) (tape : Fin 3 → OTerm α)
    (fact : Nonempty (Derivation B Γ (programGraph i (suc z) ![tape k]))) :
    Nonempty (Derivation B Γ
      (programGraph (.composition i (fun _ : Fin 1 => .projection k)) (suc z) tape)) := by
  apply compositionValue i (fun _ : Fin 1 => .projection k) (suc z) tape ![tape k] fact
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue k tape

private theorem rewrap (i : Program 1) (r : Program 3) (x w y : OTerm α)
    (old : Nonempty (Derivation B Γ (accepts r x w y)))
    (left : Nonempty (Derivation B Γ (programGraph i (suc z) ![x])))
    (right : Nonempty (Derivation B Γ (programGraph i (suc z) ![y]))) :
    Nonempty (Derivation B Γ (accepts (withEndpointCarriers i r) x w y)) := by
  let tape : Fin 3 → OTerm α := ![x,w,y]
  rw [acceptsGraph] at old ⊢
  rw [wrapperAST]
  have l : Nonempty (Derivation B Γ (programGraph (atSource i) (suc z) tape)) :=
    writeSlot i (0 : Fin 3) tape left
  have rgt : Nonempty (Derivation B Γ (programGraph (atTarget i) (suc z) tape)) :=
    writeSlot i (2 : Fin 3) tape right
  exact conjunctionAccept r (conjunction (atSource i) (atTarget i)) tape old
    (conjunctionAccept (atSource i) (atTarget i) tape l rgt)

theorem openTransitive : ExactOpenEndpointRefinedAddressTransitivity := by
  intro i cv tv raw least B α Γ left first middle second right
  dsimp only
  intro one two
  let old := addressPositive cv tv raw least
  let R := withEndpointCarriers i old
  rw [acceptsGraph] at one two
  obtain ⟨leftPath⟩ := exact_OpenPositiveEndpointCarrierGraphs i old B α Γ
    left first middle one
  obtain ⟨rightPath⟩ := exact_OpenPositiveEndpointCarrierGraphs i old B α Γ
    middle second right two
  have oldOne : Nonempty (Derivation B Γ (accepts old left first middle)) := by
    rw [acceptsGraph]
    exact ⟨Derivation.conjunctionLeft leftPath⟩
  have oldTwo : Nonempty (Derivation B Γ (accepts old middle second right)) := by
    rw [acceptsGraph]
    exact ⟨Derivation.conjunctionLeft rightPath⟩
  have start : Nonempty (Derivation B Γ (programGraph i (suc z) ![left])) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight leftPath)⟩
  have finish : Nonempty (Derivation B Γ (programGraph i (suc z) ![right])) :=
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight rightPath)⟩
  have joined := combine cv tv raw least left first middle second right oldOne oldTwo
  apply consume old left right (suppliedEdge R left right) joined
  intro β j Δ w keeps actual
  rw [suppliedEdgeRename]
  have carriedLeft : Nonempty (Derivation B Δ (programGraph i (suc z) ![left.relabel j])) := by
    simpa only [programRename,sucRelabel,zRelabel,unaryRename] using renameInto start j Δ keeps
  have carriedRight : Nonempty (Derivation B Δ (programGraph i (suc z) ![right.relabel j])) := by
    simpa only [programRename,sucRelabel,zRelabel,unaryRename] using renameInto finish j Δ keeps
  exact provide R (left.relabel j) w (right.relabel j)
    (rewrap i old (left.relabel j) w (right.relabel j) actual carriedLeft carriedRight)

end
end LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTransitivityAddressProof
