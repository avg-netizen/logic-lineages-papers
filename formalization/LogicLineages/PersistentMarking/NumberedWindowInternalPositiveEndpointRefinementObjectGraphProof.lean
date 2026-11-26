module
public import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementObjectGraphProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAtomicRefinement (atSource atTarget)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalPositiveEndpointRefinement (withEndpointCarriers)
open NumberedWindowInternalPositiveEndpointRefinementObjectTargets

private theorem wrapperAST (i : Program 1) (r : Program 3) :
    withEndpointCarriers i r = conjunction r (conjunction (atSource i) (atTarget i)) := by
  simp only [withEndpointCarriers,exact_DispatchControlAST.2.2.2.2.2]

section
attribute [local irreducible] programGraph

private theorem readSlot {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (i : Program 1) (k : Fin 3) (tape : Fin 3 → OTerm α)
    (seen : Nonempty (Derivation B Γ
      (programGraph (.composition i (fun _ : Fin 1 => .projection k)) (suc z) tape))) :
    Nonempty (Derivation B Γ (programGraph i (suc z) ![tape k])) := by
  apply compositionRecover i (fun _ : Fin 1 => .projection k) (suc z) tape ![tape k] seen
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue k tape

theorem exactGraphs : ExactOpenPositiveEndpointCarrierGraphs := by
  intro i r B α Γ x w y
  dsimp only
  intro seen
  let tape : Fin 3 → OTerm α := ![x,w,y]
  change Nonempty (Derivation B Γ (programGraph (withEndpointCarriers i r) (suc z) tape)) at seen
  rw [wrapperAST] at seen
  obtain ⟨facts⟩ := conjunctionRecover r (conjunction (atSource i) (atTarget i)) tape seen
  obtain ⟨both⟩ := conjunctionRecover (atSource i) (atTarget i) tape
    ⟨Derivation.conjunctionRight facts⟩
  obtain ⟨left⟩ := readSlot i (0 : Fin 3) tape ⟨Derivation.conjunctionLeft both⟩
  obtain ⟨right⟩ := readSlot i (2 : Fin 3) tape ⟨Derivation.conjunctionRight both⟩
  change Nonempty (Derivation B Γ
    (programGraph r (suc z) tape ⊓ (programGraph i (suc z) ![tape 0] ⊓
      programGraph i (suc z) ![tape 2])))
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft facts)
    (Derivation.conjunctionIntroduction left right)⟩

end
end LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementObjectGraphProof
