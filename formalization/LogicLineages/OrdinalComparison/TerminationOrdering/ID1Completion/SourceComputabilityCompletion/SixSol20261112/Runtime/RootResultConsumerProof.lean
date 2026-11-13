module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SourceRootProjectionSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultConsumerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open RootResultDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem weakenConsumer (R : Program 2) (packed parameter output : OTerm alpha) (psi : Formula alpha)
 {Theta : List (Formula alpha)} (next : ReturnConsumer R body Delta packed parameter output psi)
 (inc : ∀ f ∈ Delta, f ∈ Theta) : ReturnConsumer R body Theta packed parameter output psi := by
 intro beta j Xi input work results frame payload hinc hs hw hf hr hp hq ht
 exact next beta j Xi input work results frame payload (fun f h => hinc f (inc f h)) hs hw hf hr hp hq ht
theorem renameConsumer (R : Program 2) (packed parameter output : OTerm alpha) (psi : Formula alpha)
 {beta : Type} (j : alpha → beta) (Theta : List (Formula beta))
 (next : ReturnConsumer R body Delta packed parameter output psi)
 (inc : ∀ f ∈ Delta, f.relabel j ∈ Theta) :
 ReturnConsumer R body Theta (packed.relabel j) (parameter.relabel j) (output.relabel j) (psi.relabel j) := by
 intro gamma k Xi input work results frame payload hinc hs hw hf hr hp hq ht
 have h := next gamma (k ∘ j) Xi input work results frame payload
   (by
     intro f hf
     simpa only [← InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hinc _ (inc f hf))
   hs hw hf hr
   (by simpa only [Term.relabel_relabel] using hp)
   (by simpa only [Term.relabel_relabel] using hq)
   (by simpa only [Term.relabel_relabel] using ht)
 simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using h

theorem allFuel (R : Program 2)
 (packed parameter output count input work results frame payload : OTerm alpha) (psi : Formula alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame (numeral 0))))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role (numeral 0) input)))
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.packed packed input)))
 (hq : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.parameter parameter input)))
 (hrun : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output count input)))
 (he : Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty output)))
 (next : ReturnConsumer R body Delta packed parameter output psi) : Nonempty (Derivation body Delta psi) := by
 apply zeroSuccessorCases Delta count psi
 · let A := eqn count z
   have inc : ∀ f ∈ Delta, f ∈ A :: Delta := fun f h => List.mem_cons_of_mem _ h
   have hz : Nonempty (Derivation body (A :: Delta) (eqn count z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hzero := headTransport (OriginalHereditaryRuntimeIterationDefinitions.run R) output count z (Fin.cons input Fin.elim0)
     hz (weakenProof hrun inc)
   have heq := InternalNumericIterationSupportProof.repeatZeroRecover (OriginalHereditaryCombinedStep.step R) output input hzero
   have hempty := headTransport InternalUnpair.left z output input Fin.elim0 heq (weakenProof he inc)
   exact SuffixExitCore.emptyContradiction input work results frame (numeral 0) psi (weakenProof hs inc) (weakenProof hw inc) hempty
 · intro beta j Theta extra hinc hcount
   have hs' := renameInto hs j Theta hinc
   have hw' := renameInto hw j Theta hinc
   have hf' := renameInto hf j Theta hinc
   have hr' := renameInto hr j Theta hinc
   have hp' := renameInto hp j Theta hinc
   have hq' := renameInto hq j Theta hinc
   have hrun' := renameInto hrun j Theta hinc
   simp only [graph1Rename,graph2Rename,numeralRename] at hs' hw' hf' hr' hp' hq' hrun'
   have hsucc := headTransport (OriginalHereditaryRuntimeIterationDefinitions.run R) (output.relabel j)
     (count.relabel j) (suc extra) (Fin.cons (input.relabel j) Fin.elim0) hcount hrun'
   have hreturn := andRight (RootReturnProof.positiveReturnState R body beta Theta
     (input.relabel j) (work.relabel j) (results.relabel j) (frame.relabel j) (payload.relabel j) extra (output.relabel j)
     hs' hw' hf' hr' hsucc)
   exact next beta j Theta (input.relabel j) (work.relabel j) (results.relabel j) (frame.relabel j) (payload.relabel j)
     hinc hs' hw' hf' hr' hp' hq' hreturn

theorem anchorConsumer (R : Program 2)
 (packed parameter output suffix frame payload parent counts typed typ rawJob raw : OTerm alpha) (psi : Formula alpha)
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode suffix frame (numeral 0))))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hpay : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload parent counts)))
 (hparent : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parent (numeral 0) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (next : ReturnConsumer R body Delta packed parameter output psi) :
 SuffixExitWorkingTargets.Consumer R body Delta suffix output psi := by
 intro beta j Theta count input results hinc hs hrun he
 have hw' := renameInto hw j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have hpay' := renameInto hpay j Theta hinc
 have hparent' := renameInto hparent j Theta hinc
 have ht' := renameInto ht j Theta hinc
 have hr' := renameInto hr j Theta hinc
 have hp' := renameInto hp j Theta hinc
 simp only [graph1Rename,graph2Rename,numeralRename] at hw' hf' hpay' hparent' ht' hr' hp'
 have hworkZ : Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode (suffix.relabel j) (frame.relabel j) z)) := by
   simpa only [SourceRootProjectionSupport.zeroEq] using hw'
 have hparentZ : Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (parent.relabel j) z (typed.relabel j))) := by
   simpa only [SourceRootProjectionSupport.zeroEq] using hparent'
 have hselectors := SourceRootProjectionSupport.rootSelectors input (suffix.relabel j) results (frame.relabel j)
   (payload.relabel j) (parent.relabel j) (counts.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j)
   (raw.relabel j) (parameter.relabel j) (packed.relabel j) hs hworkZ hf' hpay' hparentZ ht' hr' hp'
 have hrole : Nonempty (Derivation body Theta (graph1 OriginalHereditaryReturnStep.role (numeral 0) input)) := by
   simpa only [SourceRootProjectionSupport.zeroEq] using andLeft hselectors
 exact allFuel R (packed.relabel j) (parameter.relabel j) (output.relabel j) count input (suffix.relabel j) results
   (frame.relabel j) (payload.relabel j) (psi.relabel j) hs hw' hf' hrole (andLeft (andRight hselectors))
   (andRight (andRight hselectors)) hrun he (renameConsumer R packed parameter output psi j Theta next hinc)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultConsumerProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultConsumerProof
