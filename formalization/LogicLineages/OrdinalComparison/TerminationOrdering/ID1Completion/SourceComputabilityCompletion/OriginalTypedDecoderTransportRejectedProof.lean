module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportTagSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceRejectedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportRejectedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open OriginalTypedDecoderStepSpecification
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNe)
open OriginalTypedDecoderTransport OriginalTypedDecoderTransportLogicalProof
open InternalQuotientComparisonProof (orLeft orRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem termForbidden (H : Program 1) (raw tag payload typ gamma : OTerm alpha) (psi : Formula alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw tag payload)))
    (hb : Nonempty (Derivation body Delta
      (equal tag (numeral 6) ⊔ (equal tag (numeral 7) ⊔ StepUnknownTag tag))))
    (ha : Nonempty (Derivation body Delta (Accepted H false typ raw gamma))) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨h⟩ := OriginalTypedDecoderInternalAcceptanceRejectedProof.termRejected H raw tag payload typ gamma hp hb ha
  exact ⟨Derivation.explosion h⟩

theorem termSix (H : Program 1) (raw payload typ gamma : OTerm alpha) (psi : Formula alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 6) payload)))
    (ha : Nonempty (Derivation body Delta (Accepted H false typ raw gamma))) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨he⟩ := equalReflexive (body := body) (Delta := Delta) (numeral 6 : OTerm alpha)
  exact termForbidden H raw (numeral 6) payload typ gamma psi hp ⟨orLeft he⟩ ha

theorem termSeven (H : Program 1) (raw payload typ gamma : OTerm alpha) (psi : Formula alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 7) payload)))
    (ha : Nonempty (Derivation body Delta (Accepted H false typ raw gamma))) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨he⟩ := equalReflexive (body := body) (Delta := Delta) (numeral 7 : OTerm alpha)
  exact termForbidden H raw (numeral 7) payload typ gamma psi hp ⟨orRight (orLeft he)⟩ ha

theorem argumentsOther (H : Program 1) (tag : Nat) (h6 : tag ≠ 6) (h7 : tag ≠ 7)
    (raw payload typ gamma : OTerm alpha) (psi : Formula alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral tag) payload)))
    (ha : Nonempty (Derivation body Delta (Accepted H true typ raw gamma))) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨h⟩ := OriginalTypedDecoderInternalAcceptanceRejectedProof.argumentsRejected H raw (numeral tag)
    payload typ gamma hp (andIntro (numeralNe tag 6 h6) (numeralNe tag 7 h7)) ha
  exact ⟨Derivation.explosion h⟩

theorem unknown (H : Program 1) (arguments : Bool) (raw tag payload typ gamma : OTerm alpha)
    (psi : Formula alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw tag payload)))
    (hu : Nonempty (Derivation body Delta (StepUnknownTag tag)))
    (ha : Nonempty (Derivation body Delta (Accepted H arguments typ raw gamma))) :
    Nonempty (Derivation body Delta psi) := by
  cases arguments
  · obtain ⟨hu⟩ := hu
    exact termForbidden H raw tag payload typ gamma psi hp ⟨orRight (orRight hu)⟩ ha
  · have hh := andRight (andRight (andRight (andRight (andRight (andRight hu)))))
    obtain ⟨h⟩ := OriginalTypedDecoderInternalAcceptanceRejectedProof.argumentsRejected H raw tag payload typ gamma hp hh ha
    exact ⟨Derivation.explosion h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportRejectedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportRejectedProof
