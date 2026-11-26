module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.ComputabilityLeastTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingMembershipProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterCarrierProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterWindowProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceComputabilityLeastMembershipProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalComputabilityApplication InternalComputabilityApplicationSyntaxProof
open InternalComputabilityDownwardSyntaxProof (typedRename)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andLeft)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalOriginalUniformApplicationTypingMembershipProof
open InternalTagArithmeticSupportProof (sucNeZeroApply)
open InternalTagArithmeticSyntaxProof (OTerm z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- A false CLOSED membership test conflicts with actual typed acceptance.
The contradiction stays inside the original calculus under arbitrary Delta;
no native membership fact is reflected from an internal derivation. -/
theorem typedOutOfWindow (n : Nat) (arity : Fin n → Nat) (base : Data)
    (hbase : InternalOriginalUniformDescentSelection.Calibrated n arity base)
    (window : Program 1) (hwindow : Path.windowCalibrated n window)
    (oldComp : JointGammaComputability.Data) (oldVertex oldResult : Program 5)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) (tau : Ty) (hnot : tau ∉ S)
    (object : OTerm α) (psi : Formula α)
    (ht : Nonempty (Derivation body Delta
      (typed (OuterSelection.computability oldComp base window oldVertex oldResult)
        tau (numeral (OrdinaryArithmeticQuotient.contextCode symbols S table)) object))) :
    Nonempty (Derivation body Delta psi) := by
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let data := OuterSelection.data base window
  apply OuterCarrierSupportProof.objectCases context object psi
  intro β j gamma payload parameter Theta hj hg hr hp
  have ht' := renameInto ht j Theta hj
  simp only [typedRename, numeralRename] at ht'
  have hw := GuardedSourceCertificateProof.windowNumeral
    (body := body) (Gamma := Theta) (α := β) window context
    (OuterWindowProof.closedWindowEvaluation n window hwindow symbols S table hS)
  have rawTyped := OuterCarrierSupportProof.typedRecover oldComp data window oldVertex oldResult
    context (numeral (NumberedLeastCodeRepresentative.typeNumber tau))
    (object.relabel j) gamma payload parameter hw hg hr hp ht'
  have factors := InternalOriginalUniformDescentSelectionInternalProof.typedRecover
    data.oldRepresentative (InternalOriginalUniformDescentSelection.validity data)
    data.member payload (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) parameter rawTyped
  have hm : Nonempty (Derivation body Theta
      (graph2 (InternalOriginalUniformContextMembership.normalizeData base).member (suc z)
        (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) parameter)) := andLeft factors
  have hZero : (numeral 0 : OTerm β) = z := by rw [numeral]
  have hz : Nonempty (Derivation body Theta
      (graph2 (InternalOriginalUniformContextMembership.normalizeData base).member z
        (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) parameter)) := by
    simpa only [hnot, decide_false, Bool.toNat_false, hZero,
      InternalOriginalUniformApplicationTyping.memberGraph] using
      membershipAtParameter n arity base hbase symbols S table tau parameter gamma hp
  obtain ⟨he⟩ := valueUnique (InternalOriginalUniformContextMembership.normalizeData base).member
    (suc z) z (Fin.cons (numeral (NumberedLeastCodeRepresentative.typeNumber tau))
      (Fin.cons parameter Fin.elim0)) hm hz
  exact ⟨Derivation.explosion (sucNeZeroApply he)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceComputabilityLeastMembershipProof
