module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.UnaryDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardChoiceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardPairProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ClauseUnaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open Continuation20261115
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open DispatchFrame
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {n : Nat} {H : Program 1} {arguments : Bool} {body : Positive (Fin 1)}
  {alpha : Type} {Delta : List (Formula alpha)}

theorem atLambda (f : Frame n H arguments body alpha Delta) (tag payload first head : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing f.raw tag payload)))
    (hf : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) first f.raw))) :
    Nonempty (Derivation body Delta ((eqn tag (numeral 1) ⊓ graph1 (OriginalCodeValidityGuard.check n) (numeral 1) first).imp f.conclusion)) := by
  let A := eqn tag (numeral 1) ⊓ graph1 (OriginalCodeValidityGuard.check n) (numeral 1) first
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := UnaryDispatchProof.lambdaCode (f.addHyp A) payload first
    (OriginalEnumerationMembership.GuardPairProof.pairLiteral f.raw tag payload 1 (withHyp hp A) (andLeft h))
    (withHyp hf A) (andRight h)
  exact ⟨Derivation.implicationIntroduction d⟩

theorem atOrdinary (f : Frame n H arguments body alpha Delta) (tag payload first head : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing f.raw tag payload)))
    (hf : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) first f.raw))) :
    Nonempty (Derivation body Delta ((eqn tag (numeral 4) ⊓ (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head ⊓ graph1 (OriginalCodeValidityGuard.check n) (numeral 1) first)).imp f.conclusion)) := by
  let A := eqn tag (numeral 4) ⊓ (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head ⊓ graph1 (OriginalCodeValidityGuard.check n) (numeral 1) first)
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := UnaryDispatchProof.ordinary (f.addHyp A) payload first
    (OriginalEnumerationMembership.GuardPairProof.pairLiteral f.raw tag payload 4 (withHyp hp A) (andLeft h))
    (withHyp hf A) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ClauseUnaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ClauseUnaryProof
