module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionDefinitions
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Literal stored type/raw/parameter of the unchanged annotated job encoding
pair(role,pair(type,pair(raw,parameter))). No role check or semantic decoder. -/
def jobType : Program 1 := leftOf (rightOf (.projection 0))
def jobRaw : Program 1 := leftOf (rightOf (rightOf (.projection 0)))
def jobParameter : Program 1 := rightOf (rightOf (rightOf (.projection 0)))
def jobPacked : Program 1 := pairOf jobType jobRaw
/-- A fixed Q call at the actual type/raw repacking and original stored parameter.
The term-role annotation is established by the caller's genuine decorate graph,
not assumed as a native semantic predicate or inserted into the evaluator. -/
def scalarFromJob (Q : Program 2) : Program 1 :=
  .composition Q ![jobPacked,jobParameter]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionDefinitions
