module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.NumberedDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardChoiceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardPairProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ClauseNumberedProof
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

theorem atNumbered (f : Frame n H arguments body alpha Delta) (tag payload first second head : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing f.raw tag payload)))
    (hf : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) first f.raw)))
    (hs : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.secondOf (.projection 0)) second f.raw))) :
    Nonempty (Derivation body Delta ((eqn tag (numeral 5) ⊓ ((graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head ⊓ graph1 (OriginalCodeValidityGuard.check n) (numeral 1) first) ⊓ graph1 (OriginalCodeValidityGuard.check n) (numeral 1) second)).imp f.conclusion)) := by
  let A := eqn tag (numeral 5) ⊓ ((graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head ⊓ graph1 (OriginalCodeValidityGuard.check n) (numeral 1) first) ⊓ graph1 (OriginalCodeValidityGuard.check n) (numeral 1) second)
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := NumberedDispatchProof.numbered (f.addHyp A) payload first second
    (OriginalEnumerationMembership.GuardPairProof.pairLiteral f.raw tag payload 5 (withHyp hp A) (andLeft h))
    (withHyp hf A) (withHyp hs A) (andRight (andLeft (andRight h))) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction d⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ClauseNumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ClauseNumberedProof
