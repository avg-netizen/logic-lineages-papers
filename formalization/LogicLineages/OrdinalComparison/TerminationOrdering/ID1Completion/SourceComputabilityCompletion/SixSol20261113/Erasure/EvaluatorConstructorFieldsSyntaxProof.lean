module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorFieldsSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open GuardedSourceSyntaxProof (numeralRename)
open OriginalContextInsertionSyntaxProof (lengthRename)
open EvaluatorErasureSyntax (admittedRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorConstructorInductionDefinitions
theorem applicationRename {alpha beta : Type} (R : Program 2) (H G : Program 1) (M W : Program 2)
 (count : OTerm alpha) (xs : Fin 16 → OTerm alpha) (j : alpha → beta) :
 (applicationFields R H G M W count xs).relabel j =
 applicationFields R H G M W (count.relabel j) (fun i => (xs i).relabel j) := by
 simp only [applicationFields,InternalApplicationValidityClosure.applicationConstructors,
   conjunctionRename,graph1Rename,graph2Rename,graph3Rename,graph4Rename,
   numeralRename,admittedRename,lengthRename]
theorem lambdaRename {alpha beta : Type} (R : Program 2) (H G : Program 1) (M W : Program 2)
 (count : OTerm alpha) (xs : Fin 11 → OTerm alpha) (j : alpha → beta) :
 (lambdaFields R H G M W count xs).relabel j =
 lambdaFields R H G M W (count.relabel j) (fun i => (xs i).relabel j) := by
 simp only [lambdaFields,InternalApplicationValidityClosure.applicationConstructors,
   conjunctionRename,graph1Rename,graph2Rename,graph3Rename,graph4Rename,
   numeralRename,admittedRename,lengthRename]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorFieldsSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorFieldsSyntaxProof
