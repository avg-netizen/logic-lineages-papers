module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryAcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBinaryAcceptanceProof
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
open OriginalUniverseDecoderInternalAcceptanceBinaryProof
  (actualOriginalUniverseInternalApplicationAcceptance actualOriginalUniverseInternalNumberedAcceptance
    actualOriginalUniverseInternalConsAcceptance)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedDecoderTransportBinaryAcceptanceProof (tupleSixRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem applicationIff (H : Program 1) (M W : Program 2) (raw domain fn arg typ arrow gamma c : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw domain fn arg)))
    (ht : Nonempty (Derivation body Delta (StepCons arrow domain typ))) :
    Nonempty (Derivation body Delta
      ((Accepted H M W false typ raw gamma c).iff
        (graph2 M (numeral 1) typ c ⊓
          (Accepted H M W false arrow fn gamma c ⊓ Accepted H M W false domain arg gamma c)))) := by
  apply payloadCases raw
  intro beta j Theta payload hj hp
  simp only [iffRename,acceptedRename,graph2Rename,conjunctionRename,numeral,sucRelabel,zRelabel]
  have hc' := renameInto hc j Theta hj
  have ht' := renameInto ht j Theta hj
  rw [graph3Rename] at hc'
  rw [stepConsRename] at ht'
  have hf := applicationPairs (raw.relabel j) payload (domain.relabel j) (fn.relabel j) (arg.relabel j) hc' hp
  exact closedApply (actualOriginalUniverseInternalApplicationAcceptance body H M W beta
    (raw.relabel j) payload (domain.relabel j) (fn.relabel j) (arg.relabel j)
    (typ.relabel j) (arrow.relabel j) (gamma.relabel j) (c.relabel j))
    (andIntro (andLeft hf) (andIntro (andRight hf) ht'))

theorem numberedIff (H : Program 1) (M W : Program 2)
    (raw label head recorded base extraTypes extras headData headResult baseTypes typ gamma c : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph numberedConstructor raw ![label,head,recorded,base,extraTypes,extras])))
    (hh : Nonempty (Derivation body Delta (graph1 H headData head)))
    (ht : Nonempty (Derivation body Delta (StepArrowFields headData headResult baseTypes))) :
    Nonempty (Derivation body Delta
      ((Accepted H M W false typ raw gamma c).iff
        (graph2 M (numeral 1) typ c ⊓
          (graph2 W (numeral 1) head c ⊓
            ((equal headData (numeral 0)).not ⊓
          (equal recorded typ ⊓
            (Accepted H M W true baseTypes base gamma c ⊓ Accepted H M W true extraTypes extras gamma c))))))) := by
  apply payloadCases raw
  intro beta j Theta payload hj hp
  simp only [iffRename,acceptedRename,graph2Rename,conjunctionRename,notRename,equalRename,numeral,sucRelabel,zRelabel]
  have hc' := renameInto hc j Theta hj
  have hh' := renameInto hh j Theta hj
  have ht' := renameInto ht j Theta hj
  simp only [programRename,tupleSixRename] at hc'
  rw [graph1Rename] at hh'
  rw [stepArrowFieldsRename] at ht'
  have hf := numberedPairs (raw.relabel j) payload (label.relabel j) (head.relabel j)
    (recorded.relabel j) (base.relabel j) (extraTypes.relabel j) (extras.relabel j) hc' hp
  exact closedApply (actualOriginalUniverseInternalNumberedAcceptance body H M W beta
    (raw.relabel j) payload (label.relabel j) (head.relabel j) (recorded.relabel j)
    (base.relabel j) (extraTypes.relabel j) (extras.relabel j) (headData.relabel j)
    (headResult.relabel j) (baseTypes.relabel j) (typ.relabel j) (gamma.relabel j) (c.relabel j))
    (andIntro (andLeft hf) (andIntro (andRight hf) (andIntro hh' ht')))

theorem consIff (H : Program 1) (M W : Program 2)
    (raw domain head tail types requestedDomain tailTypes gamma c : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw domain head tail)))
    (ht : Nonempty (Derivation body Delta (StepArrowFields types requestedDomain tailTypes))) :
    Nonempty (Derivation body Delta
      ((Accepted H M W true types raw gamma c).iff
        ((equal types (numeral 0)).not ⊓
          (equal requestedDomain domain ⊓
            (Accepted H M W false domain head gamma c ⊓ Accepted H M W true tailTypes tail gamma c))))) := by
  apply payloadCases raw
  intro beta j Theta payload hj hp
  simp only [iffRename,acceptedRename,graph2Rename,conjunctionRename,notRename,equalRename,numeral,sucRelabel,zRelabel]
  have hc' := renameInto hc j Theta hj
  have ht' := renameInto ht j Theta hj
  rw [graph3Rename] at hc'
  rw [stepArrowFieldsRename] at ht'
  have hf := consPairs (raw.relabel j) payload (domain.relabel j) (head.relabel j) (tail.relabel j) hc' hp
  exact closedApply (actualOriginalUniverseInternalConsAcceptance body H M W beta
    (raw.relabel j) payload (domain.relabel j) (head.relabel j) (tail.relabel j)
    (types.relabel j) (requestedDomain.relabel j) (tailTypes.relabel j) (gamma.relabel j) (c.relabel j))
    (andIntro (andLeft hf) (andIntro (andRight hf) ht'))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBinaryAcceptanceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBinaryAcceptanceProof
