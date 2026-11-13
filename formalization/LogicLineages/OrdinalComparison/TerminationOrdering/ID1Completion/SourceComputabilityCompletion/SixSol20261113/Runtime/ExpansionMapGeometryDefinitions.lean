module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeel (graph5)
open InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Actual child-prefix observation geometry for an arbitrary parent role and
arbitrary unary observer. All supplied rows retain their literal identity.
Deletion-prefix content is not asserted here; only its exact length and position. -/
def Geometry {alpha : Type} (F : Program 1)
 (role typ raw parameter children deletions produced rawJobs annotatedPrefix childRow backwardChildren deletionPrefix : OTerm alpha) : Formula alpha :=
 graph2 OriginalHereditaryExpansion.expansion rawJobs raw parameter ⊓
 (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix children role typ raw rawJobs ⊓
 (graph1 (InternalListMap.map (k := 0) F) childRow annotatedPrefix ⊓
 (OriginalContextInsertion.lengthGraph children childRow ⊓
 (graph1 OriginalTypedArgumentObservations.reverse backwardChildren childRow ⊓
 (OriginalContextInsertion.lengthGraph deletions deletionPrefix ⊓
 (graph2 InternalApplicationValidityStackAppend.append produced deletionPrefix backwardChildren ⊓
  OriginalContextInsertion.lengthGraph (add children deletions) produced))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryDefinitions
