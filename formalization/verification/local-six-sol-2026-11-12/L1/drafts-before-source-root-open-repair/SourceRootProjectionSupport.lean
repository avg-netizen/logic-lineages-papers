module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SourceRootProjectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootReturnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SuffixExitProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SourceRootProjectionSupport
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (zeroSuccessorCases)
open OriginalHereditaryPotentialCompletionSyntaxProof (emptyRename)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem rootSelectors (input work results frame payload parent counts typed typ rawJob raw parameter packed : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame z)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hpay : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload parent counts)))
 (hparent : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parent z typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw))) :
 Nonempty (Derivation body Delta
   (graph1 OriginalHereditaryReturnStep.role z input ⊓
    (graph1 OriginalHereditaryReturnStep.packed packed input ⊓
     graph1 OriginalHereditaryReturnStep.parameter parameter input))) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
 have hwork := OriginalHereditaryInternalVisitSupportProof.workGraph input work results hs
 have hframe : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.frame frame input)) :=
   unaryValue InternalListCodec.headCode OriginalHereditaryReturnStep.work frame work xs
     (InternalRawListRecursionSupportProof.consHead work frame z hw) hwork
 have hpayload := unaryValue InternalUnpair.right OriginalHereditaryReturnStep.frame payload frame xs
   (pairRight frame (numeral 1) payload hf) hframe
 have hjob := unaryValue InternalUnpair.left OriginalHereditaryReturnStep.payload parent payload xs
   (pairLeft payload parent counts hpay) hpayload
 have hrole := unaryValue InternalUnpair.left OriginalHereditaryReturnStep.parent z parent xs
   (pairLeft parent z typed hparent) hjob
 have htyped := unaryValue InternalUnpair.right OriginalHereditaryReturnStep.parent typed parent xs
   (pairRight parent z typed hparent) hjob
 have htyp := unaryValue InternalUnpair.left (rightOf OriginalHereditaryReturnStep.parent) typ typed xs
   (pairLeft typed typ rawJob ht) htyped
 have hrawJob := unaryValue InternalUnpair.right (rightOf OriginalHereditaryReturnStep.parent) rawJob typed xs
   (pairRight typed typ rawJob ht) htyped
 have hraw := unaryValue InternalUnpair.left OriginalHereditaryReturnStep.rawJob raw rawJob xs
   (pairLeft rawJob raw parameter hr) hrawJob
 have hparameter := unaryValue InternalUnpair.right OriginalHereditaryReturnStep.rawJob parameter rawJob xs
   (pairRight rawJob raw parameter hr) hrawJob
 have hpacked := binaryValue InternalPairing.pairing OriginalHereditaryReturnStep.expectedType OriginalHereditaryReturnStep.raw
   packed typ raw xs hp htyp hraw
 exact andIntro hrole (andIntro hpacked hparameter)

theorem singletonAllFuel (R : Program 2)
 (input suffix results frame payload parent counts typed typ rawJob raw parameter packed fuel output outWork stack value old root tail : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input suffix results)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode suffix frame z)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hpay : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload parent counts)))
 (hparent : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parent z typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hrun : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output fuel input)))
 (he : Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty output)))
 (hout : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing output outWork stack)))
 (hstack : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value old)))
 (hvalue : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value root tail))) :
 Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) root packed parameter)) := by
 apply zeroSuccessorCases Delta fuel _
 · let A := eqn fuel z
   have inc : ∀ f ∈ Delta, f ∈ A :: Delta := fun f hf => List.mem_cons_of_mem _ hf
   have hz : Nonempty (Derivation body (A :: Delta) (eqn fuel z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hzero := headTransport (OriginalHereditaryRuntimeIterationDefinitions.run R) output fuel z (Fin.cons input Fin.elim0)
     hz (weakenProof hrun inc)
   have hstateEq := InternalNumericIterationSupportProof.repeatZeroRecover (OriginalHereditaryCombinedStep.step R) output input hzero
   have hempty := headTransport InternalUnpair.left z output input Fin.elim0 hstateEq (weakenProof he inc)
   exact SuffixExitCore.emptyContradiction input suffix results frame z _ (weakenProof hs inc) (weakenProof hw inc) hempty
 · intro beta j Theta extra hinc hfuel
   have hs' := renameInto hs j Theta hinc
   have hw' := renameInto hw j Theta hinc
   have hf' := renameInto hf j Theta hinc
   have hpay' := renameInto hpay j Theta hinc
   have hparent' := renameInto hparent j Theta hinc
   have ht' := renameInto ht j Theta hinc
   have hr' := renameInto hr j Theta hinc
   have hp' := renameInto hp j Theta hinc
   have hrun' := renameInto hrun j Theta hinc
   have hout' := renameInto hout j Theta hinc
   have hstack' := renameInto hstack j Theta hinc
   have hvalue' := renameInto hvalue j Theta hinc
   simp only [graph1Rename,graph2Rename,numeralRename] at hs' hw' hf' hpay' hparent' ht' hr' hp' hrun' hout' hstack' hvalue'
   have hrunSucc := headTransport (OriginalHereditaryRuntimeIterationDefinitions.run R) (output.relabel j)
     (fuel.relabel j) (suc extra) (Fin.cons (input.relabel j) Fin.elim0) hfuel hrun'
   have hselectors := rootSelectors (input.relabel j) (suffix.relabel j) (results.relabel j) (frame.relabel j)
     (payload.relabel j) (parent.relabel j) (counts.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j)
     (raw.relabel j) (parameter.relabel j) (packed.relabel j) hs' hw' hf' hpay' hparent' ht' hr' hp'
   rw [graph2Rename]
   exact RootReturnProof.positiveReturnProjection R body beta Theta (input.relabel j) (suffix.relabel j) (results.relabel j)
     (frame.relabel j) (payload.relabel j) (packed.relabel j) (parameter.relabel j) extra (output.relabel j)
     (outWork.relabel j) (stack.relabel j) (value.relabel j) (old.relabel j) (root.relabel j) (tail.relabel j)
     hs' hw' hf' (andLeft hselectors) (andLeft (andRight hselectors)) (andRight (andRight hselectors))
     hrunSucc hout' hstack' hvalue'

theorem suffixConsumer (R : Program 2)
 (suffix frame payload parent counts typed typ rawJob raw parameter packed output outWork stack value old root tail : OTerm alpha)
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode suffix frame z)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hpay : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload parent counts)))
 (hparent : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parent z typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hout : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing output outWork stack)))
 (hstack : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value old)))
 (hvalue : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value root tail))) :
 SuffixExitTargets.Consumer R body Delta suffix output (graph2 (OriginalRootObservation.rootObservation R) root packed parameter) := by
 intro beta j Theta count input results hinc hs hrun he
 have hw' := renameInto hw j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have hpay' := renameInto hpay j Theta hinc
 have hparent' := renameInto hparent j Theta hinc
 have ht' := renameInto ht j Theta hinc
 have hr' := renameInto hr j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hout' := renameInto hout j Theta hinc
 have hstack' := renameInto hstack j Theta hinc
 have hvalue' := renameInto hvalue j Theta hinc
 simp only [graph1Rename,graph2Rename,numeralRename] at hw' hf' hpay' hparent' ht' hr' hp' hout' hstack' hvalue'
 rw [graph2Rename]
 exact singletonAllFuel R input (suffix.relabel j) results (frame.relabel j) (payload.relabel j) (parent.relabel j)
   (counts.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (packed.relabel j)
   count (output.relabel j) (outWork.relabel j) (stack.relabel j) (value.relabel j) (old.relabel j) (root.relabel j) (tail.relabel j)
   hs hw' hf' hpay' hparent' ht' hr' hp' hrun he hout' hstack' hvalue'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SourceRootProjectionSupport
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SourceRootProjectionSupport
