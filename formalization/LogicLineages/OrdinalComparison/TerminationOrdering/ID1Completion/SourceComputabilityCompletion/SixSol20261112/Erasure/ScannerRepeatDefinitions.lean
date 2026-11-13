module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.ScannerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.ScannerRepeatDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Original list recursion, with both actual states and the actual runtime
parameter bound INSIDE every induction row. P is a read-only graph observer. -/
def matrix {alpha : Type} (T P : Program 2) (code : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
 (InternalParameterizedApplicationStepChecker.repeatGraph T
   (.var (.inr 1)) (code.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 2)) ⊓
  graph2 P (suc z) (.var (.inr 0)) (.var (.inr 2))).imp
 (graph2 P (suc z) (.var (.inr 1)) (.var (.inr 2)))

def row {alpha : Type} (T P : Program 2) (code : OTerm alpha) : Formula alpha :=
 InternalClosedPrograms.allBlock (matrix T P code)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.ScannerRepeatDefinitions
