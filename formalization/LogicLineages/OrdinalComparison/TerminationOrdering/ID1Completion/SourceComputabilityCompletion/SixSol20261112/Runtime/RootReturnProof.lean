module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootReturnTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalReturnRootProjectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalReturnCombinedControlProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionEmptyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootReturnProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeelSupportProof (andIntro andRight)
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof (consTermRename conjunctionRename)
open InternalTagArithmeticSupportProof (symm)
open InternalTagArithmeticSyntaxProof (sucRelabel)
open GuardedSourceSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Empty work follows from the actual popped pair, independently of every
result value and every stored child/deletion count. -/
theorem singletonEmpty (R : Program 2) (input work results frame payload output : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame (numeral 0))))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role (numeral 0) input)))
 (ht : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.step R) output input))) :
 Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty output)) := by
 have hp := OriginalInternalReturnRootProjectionSupportProof.popRecover R input work results frame (numeral 0) payload output hs hw hf hr ht
 have hz := OriginalHereditaryReturnStepInternalSupportProof.restGraph input work results frame (numeral 0) hs hw
 apply programCompositionCases InternalPairing.pairing
   ![OriginalHereditaryReturnStep.rest,consOf (OriginalHereditaryReturnStep.termValue R) OriginalHereditaryReturnStep.oldSuffix]
   output (Fin.cons input Fin.elim0) _ hp
 intro beta j ys Theta hinc hpair hfields
 rw [OriginalHereditaryPotentialCompletionSyntaxProof.emptyRename]
 have hz' := renameInto hz j Theta hinc
 simp only [graph1Rename,numeralRename] at hz'
 have hfirst : Nonempty (Derivation body Theta (graph1 OriginalHereditaryReturnStep.rest (ys 0) (input.relabel j))) := by
   simpa only [consTermRename,emptyRename,Matrix.cons_val_zero] using hfields (0 : Fin 2)
 have hpair' : Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (output.relabel j) (ys 0) (ys 1))) := by
   simpa only [graph2,OriginalRawSyntaxTransportInternalConstructorSupportProof.twoTuple] using hpair
 exact outputTransport InternalUnpair.left (ys 0) (numeral 0)
   (Fin.cons (output.relabel j) Fin.elim0)
   (valueUnique OriginalHereditaryReturnStep.rest (ys 0) (numeral 0) (Fin.cons (input.relabel j) Fin.elim0) hfirst hz')
   (pairLeft (output.relabel j) (ys 0) (ys 1) hpair')

theorem positiveReturnState : RootReturnTargets.PositiveReturnState := by
 intro R body alpha Delta input work results frame payload extra output hs hw hf hr hrun
 apply programCases (OriginalHereditaryReturnStep.step R) (Fin.cons input Fin.elim0) _
 intro beta j Theta next hinc ht
 simp only [conjunctionRename,OriginalHereditaryPotentialCompletionSyntaxProof.emptyRename,graph1Rename]
 simp only [consTermRename,emptyRename] at ht
 have hs' := renameInto hs j Theta hinc
 have hw' := renameInto hw j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have hr' := renameInto hr j Theta hinc
 have hrun' := renameInto hrun j Theta hinc
 simp only [graph1Rename,graph2Rename,numeralRename,sucRelabel] at hs' hw' hf' hr' hrun'
 have he := singletonEmpty R (input.relabel j) (work.relabel j) (results.relabel j) (frame.relabel j) (payload.relabel j) next hs' hw' hf' hr' ht
 have hc := OriginalInternalReturnCombinedControlProof.control R
   (input.relabel j) (work.relabel j) (results.relabel j) (frame.relabel j) (numeral 0) (payload.relabel j) next hs' hw' hf' ht
 have htail := InternalNumericIterationProof.frontSuccForward (OriginalHereditaryCombinedStep.step R)
   (extra.relabel j) (output.relabel j) (input.relabel j) next hc hrun'
 have hfixed := InternalNumericIterationFixedPointProof.fixedValue (OriginalHereditaryCombinedStep.step R)
   (extra.relabel j) next (OriginalHereditaryPotentialCompletionEmptyProof.fixedEmpty R next he)
 have ho := valueUnique (OriginalHereditaryRuntimeIterationDefinitions.run R) (output.relabel j) next
   (Fin.cons (extra.relabel j) (Fin.cons next Fin.elim0)) htail hfixed
 obtain ⟨ho⟩ := ho
 have hn := Nonempty.intro (symm ho)
 exact andIntro
   (headTransport InternalUnpair.left (numeral 0) next (output.relabel j) Fin.elim0 hn he)
   (outputTransport (OriginalHereditaryReturnStep.step R) next (output.relabel j) (Fin.cons (input.relabel j) Fin.elim0) hn ht)

theorem positiveReturnProjection : RootReturnTargets.PositiveReturnProjection := by
 intro R body alpha Delta input work results frame payload packed parameter extra output outWork stack value old root tail
   hs hw hf hr hp hq hrun hout hstack hvalue
 have hreturn := andRight (positiveReturnState R body alpha Delta input work results frame payload extra output hs hw hf hr hrun)
 exact OriginalInternalReturnRootProjectionProof.actualProjection R body alpha Delta
   input work results frame (numeral 0) payload packed parameter output outWork stack value old root tail
   hs hw hf hr hp hq hreturn hout hstack hvalue
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootReturnProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootReturnProof
