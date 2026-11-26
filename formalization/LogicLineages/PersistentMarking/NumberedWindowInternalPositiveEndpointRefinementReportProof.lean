module
public import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementReportTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBackwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementReportProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalAtomicRefinement (atSource atTarget)
open NumberedWindowInternalPositiveEndpointRefinement (withEndpointCarriers)
open NumberedWindowInternalPositiveEndpointRefinementObjectChecks (exact_OpenPositiveEndpointCarrierGraphs)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (someAddressPositive)
open NumberedWindowInternalSparseAddressPositiveOpenForwardProof (forward)
open NumberedWindowInternalSparseAddressPositiveOpenBackwardProof (backward)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalPositiveEndpointRefinementReportTargets

private theorem acceptsGraph {α : Type} (r : Program 3) (left witness right : OTerm α) :
    accepts r left witness right = programGraph r (suc z) ![left,witness,right] := rfl

private theorem wrapperAST (i : Program 1) (r : Program 3) :
    withEndpointCarriers i r = conjunction r (conjunction (atSource i) (atTarget i)) := by
  simp only [withEndpointCarriers,exact_DispatchControlAST.2.2.2.2.2]

section
attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem writeSlot (i : Program 1) (k : Fin 3) (tape : Fin 3 → OTerm α)
    (known : Nonempty (Derivation B Γ (programGraph i (suc z) ![tape k]))) :
    Nonempty (Derivation B Γ
      (programGraph (.composition i (fun _ : Fin 1 => .projection k)) (suc z) tape)) := by
  apply compositionValue i (fun _ : Fin 1 => .projection k) (suc z) tape ![tape k] known
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue k tape

private theorem reportOfAcceptance (i cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (left witness right : OTerm α)
    (seen : Nonempty (Derivation B Γ
      (accepts (withEndpointCarriers i (addressPositive cv tv raw least)) left witness right))) :
    Nonempty (Derivation B Γ (guardedReport i cv tv raw least left witness right)) := by
  rw [acceptsGraph] at seen
  let old := addressPositive cv tv raw least
  obtain ⟨parts⟩ := exact_OpenPositiveEndpointCarrierGraphs i old B α Γ left witness right seen
  have inner : Nonempty (Derivation B Γ (programGraph old (suc z) ![left,witness,right])) :=
    ⟨Derivation.conjunctionLeft parts⟩
  obtain ⟨report⟩ := forward cv tv raw least left witness right inner
  change Nonempty (Derivation B Γ (someAddressPositive cv tv raw least left witness right ⊓
    (programGraph i (suc z) ![left] ⊓ programGraph i (suc z) ![right])))
  exact ⟨Derivation.conjunctionIntroduction report (Derivation.conjunctionRight parts)⟩

private theorem acceptanceOfReport (i cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (left witness right : OTerm α)
    (seen : Nonempty (Derivation B Γ (guardedReport i cv tv raw least left witness right))) :
    Nonempty (Derivation B Γ
      (accepts (withEndpointCarriers i (addressPositive cv tv raw least)) left witness right)) := by
  let tape : Fin 3 → OTerm α := ![left,witness,right]
  let old := addressPositive cv tv raw least
  change Nonempty (Derivation B Γ (someAddressPositive cv tv raw least left witness right ⊓
    (programGraph i (suc z) ![left] ⊓ programGraph i (suc z) ![right]))) at seen
  obtain ⟨parts⟩ := seen
  have report : Nonempty (Derivation B Γ (someAddressPositive cv tv raw least left witness right)) :=
    ⟨Derivation.conjunctionLeft parts⟩
  have base : Nonempty (Derivation B Γ (programGraph old (suc z) tape)) :=
    backward cv tv raw least left witness right report
  have guards := Derivation.conjunctionRight parts
  have l : Nonempty (Derivation B Γ (programGraph (atSource i) (suc z) tape)) :=
    writeSlot i (0 : Fin 3) tape ⟨Derivation.conjunctionLeft guards⟩
  have r : Nonempty (Derivation B Γ (programGraph (atTarget i) (suc z) tape)) :=
    writeSlot i (2 : Fin 3) tape ⟨Derivation.conjunctionRight guards⟩
  rw [acceptsGraph,wrapperAST]
  exact conjunctionAccept old (conjunction (atSource i) (atTarget i)) tape base
    (conjunctionAccept (atSource i) (atTarget i) tape l r)

theorem openReport : ExactOpenEndpointRefinedReport := by
  intro i cv tv raw least B α Γ left witness right
  let accepted := accepts (withEndpointCarriers i (addressPositive cv tv raw least)) left witness right
  let reported := guardedReport i cv tv raw least left witness right
  have a : Derivation B (accepted :: Γ) accepted := Derivation.hypothesis List.mem_cons_self
  have r : Derivation B (reported :: Γ) reported := Derivation.hypothesis List.mem_cons_self
  obtain ⟨out⟩ := reportOfAcceptance i cv tv raw least left witness right ⟨a⟩
  obtain ⟨back⟩ := acceptanceOfReport i cv tv raw least left witness right ⟨r⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction out)
    (Derivation.implicationIntroduction back)⟩

end
end LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementReportProof
