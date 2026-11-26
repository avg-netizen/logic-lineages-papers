module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Internal finite visit content, conditional on the explicit smaller-job
completion/content suppliers. The output is the actual reversed map of the SAME
evaluator-role observer, not an arbitrary row of the right length. This helper is
not the final Job+Framed theorem; its content premise must be discharged there. -/
def ActualMappedVisits : Prop := ∀ (R : Program 2) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha)) (size jobs tagged forward produced : OTerm alpha),
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryVisitScheduler.tagVisits tagged jobs)) →
 Nonempty (Derivation body Delta (Runtime.VisitListCompletionDefinitions.AllComplete R size jobs)) →
 Nonempty (Derivation body Delta (ContentVisitsDefinitions.AllContent R size jobs)) →
 Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0)
   (FramedContentDefinitions.contentProgram R)) forward jobs)) →
 Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse produced forward)) →
 Nonempty (Derivation body Delta (ContentVisitsDefinitions.Counted R tagged produced))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsTargets
