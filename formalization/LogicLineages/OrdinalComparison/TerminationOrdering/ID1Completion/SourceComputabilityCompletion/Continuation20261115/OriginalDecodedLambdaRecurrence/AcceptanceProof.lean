module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.GuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.AcceptanceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem optionalGuard (U : Fin 19 → Program 3) (p q : Program 3)
    (node code param : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (graph3 (TransparentExchangeLayer.optional U (InternalAcceptance.conjunction p q)) (numeral 2) node code param))) :
    Nonempty (Derivation body Delta
      (graph3 (InternalAcceptance.conjunction p q) (numeral 1) node code param)) := by
  let A := graph3 (InternalAcceptance.conjunction p q) (numeral 1) node code param
  apply formulaCases A
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  · have hz := OriginalTransparentLambdaValidityInternalBranchSupportProof.conjunctionReject
      p q ![node,code,param] (show Nonempty (Derivation body (A.not :: Delta) A.not) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have hf : Nonempty (Derivation body (A.not :: Delta)
        (graph3 (TransparentExchangeLayer.optional U (InternalAcceptance.conjunction p q)) (numeral 1) node code param)) :=
      zeroBranchIntro (InternalAcceptance.conjunction p q) (InternalLessThan.constantOne 3)
        (.composition .succ (fun _ : Fin 1 => TransparentExchangeLayer.body U)) (numeral 1) ![node,code,param] hz
        (InternalLessThanSupportProof.oneConstantValue ![node,code,param])
    obtain ⟨he⟩ := valueUnique (TransparentExchangeLayer.optional U (InternalAcceptance.conjunction p q))
      (numeral 2) (numeral 1) ![node,code,param] (withHyp h A.not) hf
    exact ⟨Derivation.explosion (sucNeZeroApply (cancelSuc he))⟩

theorem layerGuard (n : Nat) (arity : Fin n → Nat) (node code param : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (graph3 (OriginalDecodedLayerCalibration.layer n arity) (numeral 2) node code param))) :
    Nonempty (Derivation body Delta
      (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node code param)) :=
  optionalGuard _ (OriginalDecodedLayerCalibration.nodeAccepted n) (OriginalDecodedLayerCalibration.windowAccepted n)
    node code param h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.AcceptanceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.AcceptanceProof
