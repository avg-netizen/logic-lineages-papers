module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportTagSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceRejectedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportRejectedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open OriginalTypedDecoderStepSpecification
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNe)
open OriginalUniverseDecoderTransport OriginalTypedDecoderTransportLogicalProof
open InternalQuotientComparisonProof (orLeft orRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem termForbidden (H : Program 1) (M W : Program 2) (raw tag payload typ gamma c : OTerm alpha) (psi : Formula alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw tag payload)))
    (hb : Nonempty (Derivation body Delta
      (equal tag (numeral 6) ⊔ (equal tag (numeral 7) ⊔ StepUnknownTag tag))))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ raw gamma c))) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨hn⟩ := closedApply
    ((OriginalUniverseDecoderInternalAcceptanceRejectedProof.actualOriginalUniverseInternalRejectedTags).1
      body H M W alpha raw tag payload typ gamma c) (andIntro hp hb)
  obtain ⟨ha⟩ := ha
  exact ⟨Derivation.explosion (Derivation.implicationElimination hn ha)⟩

theorem termSix (H : Program 1) (M W : Program 2) (raw payload typ gamma c : OTerm alpha) (psi : Formula alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 6) payload)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ raw gamma c))) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨he⟩ := equalReflexive (body := body) (Delta := Delta) (numeral 6 : OTerm alpha)
  exact termForbidden H M W raw (numeral 6) payload typ gamma c psi hp ⟨orLeft he⟩ ha

theorem termSeven (H : Program 1) (M W : Program 2) (raw payload typ gamma c : OTerm alpha) (psi : Formula alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 7) payload)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ raw gamma c))) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨he⟩ := equalReflexive (body := body) (Delta := Delta) (numeral 7 : OTerm alpha)
  exact termForbidden H M W raw (numeral 7) payload typ gamma c psi hp ⟨orRight (orLeft he)⟩ ha

theorem argumentsForbidden (H : Program 1) (M W : Program 2)
    (raw tag payload typ gamma c : OTerm alpha) (psi : Formula alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw tag payload)))
    (hb : Nonempty (Derivation body Delta
      ((equal tag (numeral 6)).not ⊓ (equal tag (numeral 7)).not)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true typ raw gamma c))) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨hn⟩ := closedApply
    ((OriginalUniverseDecoderInternalAcceptanceRejectedProof.actualOriginalUniverseInternalRejectedTags).2
      body H M W alpha raw tag payload typ gamma c) (andIntro hp hb)
  obtain ⟨ha⟩ := ha
  exact ⟨Derivation.explosion (Derivation.implicationElimination hn ha)⟩

theorem argumentsOther (H : Program 1) (M W : Program 2) (tag : Nat) (h6 : tag ≠ 6) (h7 : tag ≠ 7)
    (raw payload typ gamma c : OTerm alpha) (psi : Formula alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral tag) payload)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true typ raw gamma c))) :
    Nonempty (Derivation body Delta psi) := by
  exact argumentsForbidden H M W raw (numeral tag) payload typ gamma c psi hp
    (andIntro (numeralNe tag 6 h6) (numeralNe tag 7 h7)) ha

theorem unknown (H : Program 1) (M W : Program 2) (arguments : Bool) (raw tag payload typ gamma c : OTerm alpha)
    (psi : Formula alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw tag payload)))
    (hu : Nonempty (Derivation body Delta (StepUnknownTag tag)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W arguments typ raw gamma c))) :
    Nonempty (Derivation body Delta psi) := by
  cases arguments
  · obtain ⟨hu⟩ := hu
    exact termForbidden H M W raw tag payload typ gamma c psi hp ⟨orRight (orRight hu)⟩ ha
  · have hh := andRight (andRight (andRight (andRight (andRight (andRight hu)))))
    exact argumentsForbidden H M W raw tag payload typ gamma c psi hp hh ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportRejectedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportRejectedProof
