module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceApplicationFieldsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceCoordinatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceApplicationFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityApplicationSourceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open InternalApplicationValidityClosure
open OriginalTypedDecoderTransportLogicalProof (iffForward)
open OriginalTransparentDecoderValidatorCollapseSourceApplicationProof
open OriginalTransparentDecoderValidatorCollapseSourceCoordinatesProof
open OriginalTransparentDecoderValidatorCollapsePackedProof
open OriginalLambdaConstructorGraphSyntaxProof (oneRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem fieldsIff (H G : Program 1) (M W : Program 2)
 (arrow d e fp ap fn arg packed parameter c gamma : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (applicationConstructors arrow d e fp ap fn arg packed)))
 (hparameter : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma))) :
 Nonempty (Derivation body Delta
  ((graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter).iff
   (graph2 M (numeral 1) e c ⊓
    (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) fn parameter ⊓
     graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) arg parameter)))) := by
 apply applicationCoordinatesCases arrow d e fp ap fn arg packed _ hc
 intro beta j Theta raw middle hj hp ht hb
 simp only [OriginalTransparentLambdaStepInternalProof.iffRename,conjunctionRename,graph2Rename,oneRename]
 have hc' := renameInto hc j Theta hj
 simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
 have hparameter' := renameInto hparameter j Theta hj
 simp only [graph2Rename] at hparameter'
 exact sourceApplicationCoordinatesIff H G M W
  (packed.relabel j) (parameter.relabel j) (e.relabel j) raw middle (d.relabel j)
  (fp.relabel j) (ap.relabel j) (arrow.relabel j) (fn.relabel j) (arg.relabel j)
  (c.relabel j) (gamma.relabel j) hp ht hb (andLeft hc') (andLeft (andRight hc'))
  (andLeft (andRight (andRight hc'))) hparameter'

theorem rebuild (H G : Program 1) (M W : Program 2)
 (s t parameter fn targetFn arg arrow d e fp tp ap c gamma : OTerm alpha)
 (hcs : Nonempty (Derivation body Delta (applicationConstructors arrow d e fp ap fn arg s)))
 (hct : Nonempty (Derivation body Delta (applicationConstructors arrow d e tp ap targetFn arg t)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) s parameter)))
 (ht : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) targetFn parameter))) :
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) t parameter)) := by
 have old := iffForward (fieldsIff H G M W arrow d e fp ap fn arg s parameter c gamma hcs hp) hs
 have law := fieldsIff H G M W arrow d e tp ap targetFn arg t parameter c gamma hct hp
 obtain ⟨hb⟩ := andRight law
 obtain ⟨ha⟩ := andIntro (andLeft old) (andIntro ht (andRight (andRight old)))
 exact ⟨Derivation.implicationElimination hb ha⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityApplicationSourceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityApplicationSourceProof
