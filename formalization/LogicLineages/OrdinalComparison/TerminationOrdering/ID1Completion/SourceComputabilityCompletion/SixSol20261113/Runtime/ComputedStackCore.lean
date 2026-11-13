module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CompletedAgreementProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultSourceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackCore
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ComputedStackDefinitions ComputedStackSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem fromStates (R : Program 2) (packed parameter job visit work initial count value fuel output : OTerm alpha) (stack final : OTerm alpha)
 (hv : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit (numeral 0) job)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit (numeral 0))))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial work (numeral 0))))
 (hf : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value)))
 (hrun : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output fuel initial)))
 (he : Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty output)))
 (ho : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.completed R) output packed parameter)))
 (hs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value (numeral 0))))
 (hfinal : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing final (numeral 0) stack))) :
 Nonempty (Derivation body Delta (SingletonResult R packed parameter output)) := by
 have hrunExact := JobFrameSyntax.frameApply R job count value (numeral 0) (numeral 0) visit work initial stack final hf
   (andIntro hv (andIntro hw (andIntro hi (andIntro hs hfinal))))
 have hEmpty : Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty final)) :=
   pairLeft final (numeral 0) stack hfinal
 have heq := SixSol20261112.Runtime.CompletedAgreementProof.actualCompletedAgreement R body alpha Delta
   count fuel initial final output hrunExact hEmpty hrun he
 have hout := outputTransport InternalPairing.pairing final output (Fin.cons (numeral 0) (Fin.cons stack Fin.elim0)) heq hfinal
 let xs : Fin 2 → OTerm alpha := Fin.cons packed (Fin.cons parameter Fin.elim0)
 have hright := unaryValue InternalUnpair.right (OriginalHereditaryEvaluatorDefinitions.completed R) stack output xs
   (pairRight output (numeral 0) stack hout) ho
 have heval : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) value packed parameter)) :=
   unaryValue InternalListCodec.headCode (rightOf (OriginalHereditaryEvaluatorDefinitions.completed R)) value stack xs
     (InternalRawListRecursionSupportProof.consHead stack value (numeral 0) hs) hright
 exact shapeIntro R packed parameter output stack value (andIntro hout (andIntro hs heval))
theorem withStack (R : Program 2) (packed parameter job visit work initial count value fuel output : OTerm alpha) (stack : OTerm alpha)
 (hv : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit (numeral 0) job)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit (numeral 0))))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial work (numeral 0))))
 (hf : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value)))
 (hrun : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output fuel initial)))
 (he : Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty output)))
 (ho : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.completed R) output packed parameter)))
 (hs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value (numeral 0)))) :
 Nonempty (Derivation body Delta (SingletonResult R packed parameter output)) := by
 apply programCases InternalPairing.pairing (Fin.cons (numeral 0) (Fin.cons stack Fin.elim0)) _
 intro beta j Theta final hinc hq
 simp only [consTermRename,emptyRename,numeralRename] at hq
 rw [shapeRename]
 have hv' := renameInto hv j Theta hinc
 have hw' := renameInto hw j Theta hinc
 have hi' := renameInto hi j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have hrun' := renameInto hrun j Theta hinc
 have he' := renameInto he j Theta hinc
 have ho' := renameInto ho j Theta hinc
 have hs' := renameInto hs j Theta hinc
 simp only [graph2Rename,numeralRename,JobFrameSyntax.frameRename,OriginalHereditaryPotentialCompletionSyntaxProof.emptyRename] at hv' hw' hi' hf' hrun' he' ho' hs'
 exact fromStates R (packed.relabel j) (parameter.relabel j) (job.relabel j) (visit.relabel j) (work.relabel j) (initial.relabel j) (count.relabel j) (value.relabel j) (fuel.relabel j) (output.relabel j) (stack.relabel j) final hv' hw' hi' hf' hrun' he' ho' hs' hq
theorem fromFramed (R : Program 2) (packed parameter job visit work initial count value fuel output : OTerm alpha)
 (hv : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit (numeral 0) job)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit (numeral 0))))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial work (numeral 0))))
 (hf : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value)))
 (hrun : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output fuel initial)))
 (he : Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty output)))
 (ho : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.completed R) output packed parameter))) :
 Nonempty (Derivation body Delta (SingletonResult R packed parameter output)) := by
 apply programCases InternalListCodec.consCode (Fin.cons value (Fin.cons (numeral 0) Fin.elim0)) _
 intro beta j Theta stack hinc hq
 simp only [consTermRename,emptyRename,numeralRename] at hq
 rw [shapeRename]
 have hv' := renameInto hv j Theta hinc
 have hw' := renameInto hw j Theta hinc
 have hi' := renameInto hi j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have hrun' := renameInto hrun j Theta hinc
 have he' := renameInto he j Theta hinc
 have ho' := renameInto ho j Theta hinc
 simp only [graph2Rename,numeralRename,JobFrameSyntax.frameRename,OriginalHereditaryPotentialCompletionSyntaxProof.emptyRename] at hv' hw' hi' hf' hrun' he' ho'
 exact withStack R (packed.relabel j) (parameter.relabel j) (job.relabel j) (visit.relabel j) (work.relabel j) (initial.relabel j) (count.relabel j) (value.relabel j) (fuel.relabel j) (output.relabel j) stack hv' hw' hi' hf' hrun' he' ho' hq
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackCore
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackCore
