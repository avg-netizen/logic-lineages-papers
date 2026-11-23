module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInstalledOriginTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInstalledOriginSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique equalEqn)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalDirectSharedTapeTargets (Reports)
open ID1Completion.InternalBetaTotalityProof (addHyp)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem targetMember (raw known actual key : OTerm α)
    (knownP : Nonempty (Derivation B Γ (unary parser (suc known) raw)))
    (actualP : Nonempty (Derivation B Γ (unary parser (suc actual) raw)))
    (hit : Nonempty (Derivation B Γ (memberGraph known key))) :
    Nonempty (Derivation B Γ (memberGraph actual key)) := by
  obtain ⟨e⟩ := valueUnique parser (suc known) (suc actual) ![raw] knownP actualP
  change Nonempty (Derivation B Γ (programGraph scratchMember (suc z) ![known,key])) at hit
  change Nonempty (Derivation B Γ (programGraph scratchMember (suc z) ![actual,key]))
  unfold programGraph at hit ⊢
  apply graphInputTransport B α 2 Γ (OrdinaryArithmetic.graphFormula scratchMember)
    (suc z) ![known,key] ![actual,key] _ hit
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change Nonempty (Derivation B Γ (equal known actual))
    rw [equalEqn]
    exact ⟨cancelSuc e⟩
  · obtain rfl := Fin.eq_zero j
    change Nonempty (Derivation B Γ (equal key key))
    rw [equalEqn]
    exact ⟨ID1Completion.InternalTagArithmeticSupportProof.refl key⟩

private theorem withHyp {f : Formula α}
    (h : Nonempty (Derivation B Γ f)) (H : Formula α) :
    Nonempty (Derivation B (H :: Γ) f) := by
  obtain ⟨d⟩ := h
  exact ⟨addHyp d H⟩

theorem addReportHyp (count : Program 2) (r : Program 3)
    (src dst kept removed inserted s t k d a p sk tp : OTerm α)
    (h : Reports count count r B Γ src dst kept removed inserted s t k d a p sk tp)
    (H : Formula α) :
    Reports count count r B (H :: Γ) src dst kept removed inserted s t k d a p sk tp :=
  ⟨withHyp h.sourceParsed H,withHyp h.targetParsed H,withHyp h.keptParsed H,
    withHyp h.removedParsed H,withHyp h.insertedParsed H,withHyp h.rawProjection H,
    withHyp h.scratchProjection H,withHyp h.sourceAppend H,withHyp h.targetAppend H,
    withHyp h.sourceObserved H,withHyp h.targetObserved H,withHyp h.scanObserved H⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInstalledOriginSyntaxProof
