module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentAllChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentDependencyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Runtime FramedContentInductionDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Actual expanded dependencies complete unconditionally from original source
admission; only their CONTENT uses the strict lower-weight induction hypothesis. -/
theorem allDependencies (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B job weight jobs size : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (BelowContent R H M W c B weight)))
 (hj : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight weight job)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs))) :
 Nonempty (Derivation body Delta
   (VisitListCompletionDefinitions.AllComplete R size jobs ⊓ ContentVisitsDefinitions.AllContent R size jobs)) := by
 have hc := SourceFramedAllChildrenProof.allChildren R H M W c B job weight jobs size
   (SourceFramedProof.actualBelowCompletion R H M W body alpha Delta c B weight) hj hw he hl
 have hv := FramedContentAllChildrenProof.allChildren R H M W c B job weight jobs size hb hj hw he hl
 exact andIntro hc hv

/-- The genuine source/weight hypotheses discharge BOTH conditional finite-visit
suppliers. Every actual forward/reverse map now has a content-bearing prefix run
at that very produced row; no run or content oracle is added. -/
theorem mappedDependencies (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B job weight jobs size tagged forward produced : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (BelowContent R H M W c B weight)))
 (hj : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight weight job)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 (ht : Nonempty (Derivation body Delta (graph1 OriginalHereditaryVisitScheduler.tagVisits tagged jobs)))
 (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0)
   (FramedContentDefinitions.contentProgram R)) forward jobs)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse produced forward))) :
 Nonempty (Derivation body Delta (ContentVisitsDefinitions.Counted R tagged produced)) := by
 have hall := allDependencies R H M W c B job weight jobs size hb hj hw he hl
 exact ContentVisitsProof.actualMappedVisits R body alpha Delta size jobs tagged forward produced
   hl ht (andLeft hall) (andRight hall) hm hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentDependencyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentDependencyProof
