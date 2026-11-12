module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceApplicationFieldsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceCoordinatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceApplicationFieldsProof
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

theorem sourceChildren (H G : Program 1) (M W : Program 2)
 (arrow d e fp ap fn arg packed parameter : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (applicationConstructors arrow d e fp ap fn arg packed)))
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter))) :
 Nonempty (Derivation body Delta
  (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) fn parameter ⊓
   graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) arg parameter)) := by
 apply packedCases packed parameter
 intro beta j Theta _ _ c gamma hj _ hparameter
 simp only [conjunctionRename,graph2Rename,oneRename]
 have hc' := renameInto hc j Theta hj
 simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
 have hs' := renameInto hs j Theta hj
 simp only [graph2Rename,oneRename] at hs'
 apply applicationCoordinatesCases (arrow.relabel j) (d.relabel j) (e.relabel j)
   (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) (packed.relabel j) _ hc'
 intro beta' k Xi raw middle hk hp ht hb
 simp only [conjunctionRename,graph2Rename,oneRename]
 have hc'' := renameInto hc' k Xi hk
 simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc''
 have hs'' := renameInto hs' k Xi hk
 simp only [graph2Rename,oneRename] at hs''
 have hparameter' := renameInto hparameter k Xi hk
 rw [OriginalTypedDecoderInternalScalarSyntaxProof.stepPairRename] at hparameter'
 have factors := iffForward (sourceApplicationCoordinatesIff H G M W
   ((packed.relabel j).relabel k) ((parameter.relabel j).relabel k) ((e.relabel j).relabel k)
   raw middle ((d.relabel j).relabel k) ((fp.relabel j).relabel k) ((ap.relabel j).relabel k)
   ((arrow.relabel j).relabel k) ((fn.relabel j).relabel k) ((arg.relabel j).relabel k)
   (c.relabel k) (gamma.relabel k) hp ht hb (andLeft hc'') (andLeft (andRight hc''))
   (andLeft (andRight (andRight hc''))) hparameter') hs''
 exact andRight factors

theorem actualFieldsCases : OriginalPackedSourceApplicationFieldsTargets.ActualFieldsCases := by
 intro body alpha Delta H G M W packed parameter psi hs ht next
 apply OriginalLambdaTraversalApplicationOpeningProof.applicationCases packed parameter psi ht
 intro beta j Theta payload arrow d e fp ap fn arg hj hc _ _ _ _ _
 have hs' := renameInto hs j Theta hj
 simp only [graph2Rename,oneRename] at hs'
 have children := sourceChildren H G M W arrow d e fp ap fn arg (packed.relabel j) (parameter.relabel j) hc hs'
 exact next beta j Theta arrow d e fp ap fn arg hj hc (andLeft children) (andRight children)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceApplicationFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceApplicationFieldsProof
