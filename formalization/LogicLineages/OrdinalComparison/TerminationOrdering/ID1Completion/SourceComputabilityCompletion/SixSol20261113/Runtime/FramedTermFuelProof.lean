module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedValueTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySourceRootCompletionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedTermFuelProof
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
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem rebranch (H : Program 1) (M W : Program 2) (c B job branch : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)))
 (hb : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.branching branch job))) :
 Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c branch job)) := by
 apply OriginalHereditaryInternalAgendaBindingProof.jobCases H M W c B job _ hj
 intro beta j Theta role typ typed rawJob raw parameter gamma weight hinc fields
 rw [OriginalHereditaryInternalAgendaSyntaxProof.jobRename]
 have hb' := renameInto hb j Theta hinc
 rw [graph1Rename] at hb'
 have hweight := andLeft (andRight (andRight (andRight (andRight (andRight fields)))))
 have hbound := OriginalHereditaryInitialBranchProof.branchBound (job.relabel j) weight (branch.relabel j) hweight hb'
 exact OriginalHereditaryInternalAgendaBindingProof.jobIntro H M W (c.relabel j) (branch.relabel j) (job.relabel j)
   role typ typed rawJob raw parameter gamma weight
   (andIntro (andLeft fields) (andIntro (andLeft (andRight fields))
    (andIntro (andLeft (andRight (andRight fields)))
     (andIntro (andLeft (andRight (andRight (andRight fields))))
      (andIntro (andLeft (andRight (andRight (andRight (andRight fields))))) (andIntro hweight hbound))))))
theorem emptyAtFuel (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B job branch visit work fuel initial output : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)))
 (hb : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.branching branch job)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit (numeral 0) job)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit (numeral 0))))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial work (numeral 0))))
 (hf : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.fuel fuel job)))
 (hr : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output fuel initial))) :
 Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty output)) := by
 have ha := OriginalHereditaryInternalAgendaStructuralProof.initial body alpha Delta H M W c branch job visit work (rebranch H M W c B job branch hj hb) hv hw
 have hp := OriginalHereditaryRootPotentialProof.actualInitialPotential body alpha Delta job visit work branch fuel hv hw hb hf
 exact OriginalHereditaryPotentialActualCompletionProof.actualCompletion R H M W body alpha Delta
   c branch fuel initial work (numeral 0) fuel output
   (andIntro hi (andIntro ha (andIntro hp (andIntro (InternalCoprimeMultipleBoundedProof.selfLtSucc _) hr))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedTermFuelProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedTermFuelProof
