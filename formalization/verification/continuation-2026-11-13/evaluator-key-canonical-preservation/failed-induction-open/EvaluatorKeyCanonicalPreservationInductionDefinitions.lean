module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationInductionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorKeyPut EvaluatorKeyCanonicalInductionDefinitions (C)
def Premises {alpha : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (input out parameter : OTerm alpha) : Formula alpha :=
 Domain p H G W input parameter ⊓ graph2 (C p H G W P) out input parameter
def Result {alpha : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (input out parameter : OTerm alpha) : Formula alpha :=
 Domain p H G W out parameter ⊓ Same p H G W input out parameter
/-- All input/output/parameter variables are internal. The external compatibility
rule is used only by the step proof, never smuggled into a child premise. -/
def payloadMatrix {alpha : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (payload : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
 let input : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
 let out : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
 let parameter : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
 (graph1 InternalUnpair.right (payload.relabel Sum.inl) input).imp
  ((Premises p H G W P input out parameter).imp (Result p H G W input out parameter))
def atPayload {alpha : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (payload : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (payloadMatrix p H G W P payload)
def payloadPredicate (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 {alpha : Type} : Formula (alpha ⊕ Fin 1) := atPayload p H G W P (.var (.inr 0))
def belowPayload {alpha : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (payload : OTerm alpha) : Formula alpha := InternalStrongInduction.below (payloadPredicate p H G W P) payload
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationInductionDefinitions
