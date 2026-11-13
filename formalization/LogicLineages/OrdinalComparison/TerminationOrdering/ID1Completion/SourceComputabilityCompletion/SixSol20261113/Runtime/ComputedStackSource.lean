module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackCore
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackSource
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
theorem fromSource (R : Program 2) (body : Positive (Fin 1)) (H G : Program 1) (M W : Program 2)
 (alpha : Type) (Delta : List (Formula alpha))
 (packed parameter typ raw gamma c rawJob typed job B visit work fuel initial output : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 0) typed)))
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)))
 (hb : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.branching B job)))
 (hf : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.fuel fuel job)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit (numeral 0) job)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit (numeral 0))))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial work (numeral 0))))
 (hrun : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output fuel initial)))
 (ho : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.completed R) output packed parameter))) :
 Nonempty (Derivation body Delta (SingletonResult R packed parameter output)) := by
 have hempty := OriginalHereditarySourceRootCompletionProof.actualSourceRootCompletion R body H G M W alpha Delta
   packed parameter typ raw gamma c rawJob typed job B visit work fuel initial output hp hc hr ht hj hs hb hf hv hw hi hrun
 apply programCases OriginalHereditaryFuelProgram.weight (Fin.cons job Fin.elim0) _
 intro beta j Theta weight hinc hweight
 simp only [consTermRename,emptyRename] at hweight
 rw [shapeRename]
 have hp' := renameInto hp j Theta hinc
 have hc' := renameInto hc j Theta hinc
 have hr' := renameInto hr j Theta hinc
 have ht' := renameInto ht j Theta hinc
 have hj' := renameInto hj j Theta hinc
 have hs' := renameInto hs j Theta hinc
 have hb' := renameInto hb j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have hv' := renameInto hv j Theta hinc
 have hw' := renameInto hw j Theta hinc
 have hi' := renameInto hi j Theta hinc
 have hrun' := renameInto hrun j Theta hinc
 have ho' := renameInto ho j Theta hinc
 have hempty' := renameInto hempty j Theta hinc
 simp only [graph1Rename,graph2Rename,numeralRename,OriginalHereditaryPotentialCompletionSyntaxProof.emptyRename] at hp' hc' hr' ht' hj' hs' hb' hf' hv' hw' hi' hrun' ho' hempty'
 have hadm := OriginalHereditaryInitialBranchProof.actualJob body H G M W beta Theta
   (packed.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j) (gamma.relabel j) (c.relabel j) (rawJob.relabel j) (typed.relabel j) (job.relabel j) weight (B.relabel j) hp' hc' hr' ht' hj' hs' hweight hb'
 have hcomplete := SourceFramedProof.actualSourceFramedCompletion R H M W body beta Theta (c.relabel j) (B.relabel j) (job.relabel j) (andRight hadm)
 apply JobCompletionSyntax.completionCases R (job.relabel j) _ hcomplete
 intro gammaType k Xi count value hk hframe
 rw [shapeRename]
 have hv'' := renameInto hv' k Xi hk
 have hw'' := renameInto hw' k Xi hk
 have hi'' := renameInto hi' k Xi hk
 have hrun'' := renameInto hrun' k Xi hk
 have hempty'' := renameInto hempty' k Xi hk
 have ho'' := renameInto ho' k Xi hk
 simp only [graph2Rename,numeralRename,OriginalHereditaryPotentialCompletionSyntaxProof.emptyRename] at hv'' hw'' hi'' hrun'' hempty'' ho''
 exact ComputedStackCore.fromFramed R ((packed.relabel j).relabel k) ((parameter.relabel j).relabel k) ((job.relabel j).relabel k) ((visit.relabel j).relabel k) ((work.relabel j).relabel k) ((initial.relabel j).relabel k) count value ((fuel.relabel j).relabel k) ((output.relabel j).relabel k) hv'' hw'' hi'' hframe hrun'' hempty'' ho''
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackSource
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackSource
