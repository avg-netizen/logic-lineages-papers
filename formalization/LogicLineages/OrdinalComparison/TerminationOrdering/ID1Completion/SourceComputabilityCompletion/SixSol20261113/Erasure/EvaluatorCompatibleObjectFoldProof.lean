module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyFinalOutputDomainProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorCompatibleObjectFoldProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Context Context.EvaluatorKeyPut
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Recover the literal final-fold payload of an actual NEW Object output.
No output equality, source premise, or evaluator preservation is assumed. -/
theorem actualFold (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (context inputObject outputObject gamma raw outRaw parameter : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inputObject gamma raw)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (ho : Nonempty (Derivation body Delta (graph2 (EvaluatorKeyObjectDefinitions.object p H G W P) outputObject context inputObject)))
 (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right outRaw outputObject))) :
 Nonempty (Derivation body Delta (graph2 (EvaluatorKeyFinalFoldDefinitions.fold p H G W P) outRaw raw parameter)) := by
 apply programCases (EvaluatorKeyFinalFoldDefinitions.fold p H G W P)
   (Fin.cons raw (Fin.cons parameter Fin.elim0)) _
 intro beta j Theta actualRaw hj hf
 rw [graph2Rename]
 have hp' := renameInto hp j Theta hj
 have hparam' := renameInto hparam j Theta hj
 have ho' := renameInto ho j Theta hj
 have hr' := renameInto hr j Theta hj
 rw [graph2Rename] at hp' hparam' ho'
 rw [graph1Rename] at hr'
 simp only [consTermRename,emptyRename] at hf
 have hpair := EvaluatorKeyObjectSupportProof.outputPair (refined p H G W P)
   (context.relabel j) (inputObject.relabel j) (outputObject.relabel j) (gamma.relabel j)
   (raw.relabel j) (parameter.relabel j) actualRaw hp' hparam' hf ho'
 have he := valueUnique InternalUnpair.right actualRaw (outRaw.relabel j) (![outputObject.relabel j])
   (pairRight (outputObject.relabel j) (gamma.relabel j) actualRaw hpair) hr'
 exact outputTransport (EvaluatorKeyFinalFoldDefinitions.fold p H G W P) actualRaw (outRaw.relabel j)
   (Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorCompatibleObjectFoldProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorCompatibleObjectFoldProof
