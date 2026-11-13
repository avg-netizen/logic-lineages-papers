module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultInitialProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultLocalShapeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySourceRootCompletionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultSourceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open RootResultDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
theorem actualSourceRootReturnCases : RootResultTargets.ActualSourceRootReturnCases := by
 intro R body H G M W alpha Delta packed parameter typ raw gamma c rawJob typed job B visit work fuel initial output psi
   hp hc hr ht hj hs hb hf hv hw hi hrun next
 have hempty := OriginalHereditarySourceRootCompletionProof.actualSourceRootCompletion R body H G M W alpha Delta
   packed parameter typ raw gamma c rawJob typed job B visit work fuel initial output hp hc hr ht hj hs hb hf hv hw hi hrun
 apply programCases OriginalHereditaryFuelProgram.weight (Fin.cons job Fin.elim0) psi
 intro beta j Theta weight hinc hweight
 simp only [consTermRename,emptyRename] at hweight
 have hp' := renameInto hp j Theta hinc
 have hc' := renameInto hc j Theta hinc
 have hr' := renameInto hr j Theta hinc
 have ht' := renameInto ht j Theta hinc
 have hj' := renameInto hj j Theta hinc
 have hs' := renameInto hs j Theta hinc
 have hb' := renameInto hb j Theta hinc
 have hv' := renameInto hv j Theta hinc
 have hw' := renameInto hw j Theta hinc
 have hi' := renameInto hi j Theta hinc
 have hrun' := renameInto hrun j Theta hinc
 have he' := renameInto hempty j Theta hinc
 simp only [graph1Rename,graph2Rename,numeralRename,OriginalHereditaryPotentialCompletionSyntaxProof.emptyRename]
   at hp' hc' hr' ht' hj' hs' hb' hv' hw' hi' hrun' he'
 have ha := OriginalHereditaryInitialBranchProof.actualAgenda body H G M W beta Theta
   (packed.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j) (gamma.relabel j) (c.relabel j)
   (rawJob.relabel j) (typed.relabel j) (job.relabel j) weight (B.relabel j) (visit.relabel j) (work.relabel j)
   hp' hc' hr' ht' hj' hs' hweight hb' hv' hw'
 exact RootResultInitialProof.completed R H M W (c.relabel j) (B.relabel j) (packed.relabel j) (parameter.relabel j)
   (typ.relabel j) (raw.relabel j) (rawJob.relabel j) (typed.relabel j) (job.relabel j) (visit.relabel j)
   (work.relabel j) (initial.relabel j) (fuel.relabel j) (output.relabel j) (psi.relabel j)
   hp' hr' ht' hj' hv' hw' hi' ha hrun' he'
   (RootResultConsumerProof.renameConsumer R packed parameter output psi j Theta next hinc)
theorem actualSourceRootShape : RootResultTargets.ActualSourceRootShape := by
 intro R body H G M W alpha Delta packed parameter typ raw gamma c rawJob typed job B visit work fuel initial output
   hp hc hr ht hj hs hb hf hv hw hi hrun
 apply actualSourceRootReturnCases R body H G M W alpha Delta packed parameter typ raw gamma c rawJob typed job B visit work fuel initial output
   (Shape R packed parameter output) hp hc hr ht hj hs hb hf hv hw hi hrun
 intro beta j Theta input pending results frame payload hinc hstate hwork hframe hrole hpacked hparameter hreturn
 rw [RootResultShapeSyntax.shapeRename]
 exact RootResultLocalShapeProof.actualReturnShape R (packed.relabel j) (parameter.relabel j) (output.relabel j)
   input pending results frame payload hstate hwork hframe hrole hpacked hparameter hreturn

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem viewGraph (output stack value old root tail : OTerm alpha)
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing output (numeral 0) stack)))
 (hs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value old)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value root tail))) :
 Nonempty (Derivation body Delta (graph1 rootOfState root output)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons output Fin.elim0
 have hr := unaryValue InternalUnpair.right (.projection 0) stack output xs
   (pairRight output (numeral 0) stack ho) (projectionValue 0 xs)
 have hh := unaryValue InternalListCodec.headCode (rightOf (.projection 0)) value stack xs
   (InternalRawListRecursionSupportProof.consHead stack value old hs) hr
 exact unaryValue InternalUnpair.left rootValue root value xs (pairLeft value root tail hv) hh
theorem readbackFromShape (R : Program 2) (packed parameter output root : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (Shape R packed parameter output)))
 (hr : Nonempty (Derivation body Delta (graph1 rootOfState root output))) :
 Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) root packed parameter)) := by
 apply RootResultShapeSyntax.shapeCases R packed parameter output _ hs
 intro beta j Theta stack value old actual tail hinc hf
 have hr' := renameInto hr j Theta hinc
 rw [graph1Rename] at hr'
 have ha := viewGraph (output.relabel j) stack value old actual tail (andLeft hf)
   (andLeft (andRight hf)) (andLeft (andRight (andRight hf)))
 have he := valueUnique rootOfState actual (root.relabel j) (Fin.cons (output.relabel j) Fin.elim0) ha hr'
 rw [graph2Rename]
 exact outputTransport (OriginalRootObservation.rootObservation R) actual (root.relabel j)
   (Fin.cons (packed.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he (andRight (andRight (andRight hf)))
theorem actualSourceRootReadback : RootResultTargets.ActualSourceRootReadback := by
 intro R body H G M W alpha Delta packed parameter typ raw gamma c rawJob typed job B visit work fuel initial output root
   hp hc hr ht hj hs hb hf hv hw hi hrun hview
 exact readbackFromShape R packed parameter output root
   (actualSourceRootShape R body H G M W alpha Delta packed parameter typ raw gamma c rawJob typed job B visit work fuel initial output
     hp hc hr ht hj hs hb hf hv hw hi hrun) hview
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultSourceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultSourceProof
