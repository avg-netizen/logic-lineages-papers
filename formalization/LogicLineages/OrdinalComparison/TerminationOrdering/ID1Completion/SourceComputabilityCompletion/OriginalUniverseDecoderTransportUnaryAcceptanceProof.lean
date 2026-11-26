module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceUnaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportUnaryAcceptanceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalUniverseDecoderTransport OriginalUniverseDecoderTransportSyntaxProof
open OriginalTypedDecoderTransport (selectedMode sourceContext targetContext)
open OriginalTypedDecoderTransportConstructorProof OriginalTypedDecoderTransportLogicalProof
open OriginalUniverseDecoderInternalAcceptanceUnaryProof
  (actualOriginalUniverseInternalLambdaAcceptance actualOriginalUniverseInternalOrdinaryAcceptance)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem lambdaIff (H : Program 1) (M W : Program 2)
    (raw domain child typ requestedDomain codomain gamma bodyGamma c : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw domain child)))
    (ht : Nonempty (Derivation body Delta (StepArrowFields typ requestedDomain codomain)))
    (hg : Nonempty (Derivation body Delta (StepCons bodyGamma domain gamma))) :
    Nonempty (Derivation body Delta
      ((Accepted H M W false typ raw gamma c).iff
        (graph2 M (numeral 1) typ c ⊓
          (graph2 M (numeral 1) domain c ⊓
            ((equal typ (numeral 0)).not ⊓
          (equal requestedDomain domain ⊓ Accepted H M W false codomain child bodyGamma c)))))) := by
  apply payloadCases raw
  intro beta j Theta payload hj hp
  simp only [iffRename,acceptedRename,graph2Rename,conjunctionRename,notRename,equalRename,numeral,sucRelabel,zRelabel]
  have hc' := renameInto hc j Theta hj
  have ht' := renameInto ht j Theta hj
  have hg' := renameInto hg j Theta hj
  rw [graph2Rename] at hc'
  rw [stepArrowFieldsRename] at ht'
  rw [stepConsRename] at hg'
  have hf := lambdaPairs (raw.relabel j) payload (domain.relabel j) (child.relabel j) hc' hp
  exact closedApply (actualOriginalUniverseInternalLambdaAcceptance body H M W beta
    (raw.relabel j) payload (domain.relabel j) (child.relabel j) (typ.relabel j)
    (requestedDomain.relabel j) (codomain.relabel j) (gamma.relabel j) (bodyGamma.relabel j) (c.relabel j))
    (andIntro (andLeft hf) (andIntro (andRight hf) (andIntro ht' hg')))

theorem ordinaryIff (H : Program 1) (M W : Program 2)
    (raw head base headData result types typ gamma c : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
    (hh : Nonempty (Derivation body Delta (graph1 H headData head)))
    (ht : Nonempty (Derivation body Delta (StepArrowFields headData result types))) :
    Nonempty (Derivation body Delta
      ((Accepted H M W false typ raw gamma c).iff
        (graph2 M (numeral 1) typ c ⊓
          (graph2 W (numeral 1) head c ⊓
            ((equal headData (numeral 0)).not ⊓
          (equal result typ ⊓ Accepted H M W true types base gamma c)))))) := by
  apply payloadCases raw
  intro beta j Theta payload hj hp
  simp only [iffRename,acceptedRename,graph2Rename,conjunctionRename,notRename,equalRename,numeral,sucRelabel,zRelabel]
  have hc' := renameInto hc j Theta hj
  have hh' := renameInto hh j Theta hj
  have ht' := renameInto ht j Theta hj
  rw [graph2Rename] at hc'
  rw [graph1Rename] at hh'
  rw [stepArrowFieldsRename] at ht'
  have hf := ordinaryPairs (raw.relabel j) payload (head.relabel j) (base.relabel j) hc' hp
  exact closedApply (actualOriginalUniverseInternalOrdinaryAcceptance body H M W beta
    (raw.relabel j) payload (head.relabel j) (base.relabel j) (headData.relabel j)
    (result.relabel j) (types.relabel j) (typ.relabel j) (gamma.relabel j) (c.relabel j))
    (andIntro (andLeft hf) (andIntro (andRight hf) (andIntro hh' ht')))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportUnaryAcceptanceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportUnaryAcceptanceProof
