module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceUnaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportUnaryAcceptanceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalTypedDecoderTransport OriginalTypedDecoderTransportSyntaxProof
open OriginalTypedDecoderTransportConstructorProof OriginalTypedDecoderTransportLogicalProof
open OriginalTypedDecoderInternalAcceptanceUnaryProof
  (actualOriginalTypedInternalLambdaAcceptance actualOriginalTypedInternalOrdinaryAcceptance)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem lambdaIff (H : Program 1)
    (raw domain child typ requestedDomain codomain gamma bodyGamma : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw domain child)))
    (ht : Nonempty (Derivation body Delta (StepArrowFields typ requestedDomain codomain)))
    (hg : Nonempty (Derivation body Delta (StepCons bodyGamma domain gamma))) :
    Nonempty (Derivation body Delta
      ((Accepted H false typ raw gamma).iff
        ((equal typ (numeral 0)).not ⊓
          (equal requestedDomain domain ⊓ Accepted H false codomain child bodyGamma)))) := by
  apply payloadCases raw
  intro beta j Theta payload hj hp
  simp only [iffRename,acceptedRename,conjunctionRename,notRename,equalRename,numeral,zRelabel]
  have hc' := renameInto hc j Theta hj
  have ht' := renameInto ht j Theta hj
  have hg' := renameInto hg j Theta hj
  rw [graph2Rename] at hc'
  rw [stepArrowFieldsRename] at ht'
  rw [stepConsRename] at hg'
  have hf := lambdaPairs (raw.relabel j) payload (domain.relabel j) (child.relabel j) hc' hp
  exact closedApply (actualOriginalTypedInternalLambdaAcceptance body H beta
    (raw.relabel j) payload (domain.relabel j) (child.relabel j) (typ.relabel j)
    (requestedDomain.relabel j) (codomain.relabel j) (gamma.relabel j) (bodyGamma.relabel j))
    (andIntro (andLeft hf) (andIntro (andRight hf) (andIntro ht' hg')))

theorem ordinaryIff (H : Program 1)
    (raw head base headData result types typ gamma : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
    (hh : Nonempty (Derivation body Delta (graph1 H headData head)))
    (ht : Nonempty (Derivation body Delta (StepArrowFields headData result types))) :
    Nonempty (Derivation body Delta
      ((Accepted H false typ raw gamma).iff
        ((equal headData (numeral 0)).not ⊓
          (equal result typ ⊓ Accepted H true types base gamma)))) := by
  apply payloadCases raw
  intro beta j Theta payload hj hp
  simp only [iffRename,acceptedRename,conjunctionRename,notRename,equalRename,numeral,zRelabel]
  have hc' := renameInto hc j Theta hj
  have hh' := renameInto hh j Theta hj
  have ht' := renameInto ht j Theta hj
  rw [graph2Rename] at hc'
  rw [graph1Rename] at hh'
  rw [stepArrowFieldsRename] at ht'
  have hf := ordinaryPairs (raw.relabel j) payload (head.relabel j) (base.relabel j) hc' hp
  exact closedApply (actualOriginalTypedInternalOrdinaryAcceptance body H beta
    (raw.relabel j) payload (head.relabel j) (base.relabel j) (headData.relabel j)
    (result.relabel j) (types.relabel j) (typ.relabel j) (gamma.relabel j))
    (andIntro (andLeft hf) (andIntro (andRight hf) (andIntro hh' ht')))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportUnaryAcceptanceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportUnaryAcceptanceProof
