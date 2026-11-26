module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalInductionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorKeyPut
abbrev C (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) : Program 2 :=
 OriginalLambdaTraversalSelection.canonical (refined p H G W P).base (refined p H G W P).window
def Premises {alpha : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (left right leftOut rightOut parameter : OTerm alpha) : Formula alpha :=
 Domain p H G W left parameter ⊓ (Domain p H G W right parameter ⊓
 (Same p H G W left right parameter ⊓ (graph2 (C p H G W P) leftOut left parameter ⊓
 graph2 (C p H G W P) rightOut right parameter)))
def payloadMatrix {alpha : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (payload : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
 let left : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
 let right : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
 let leftOut : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
 let rightOut : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
 let parameter : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
 (graph1 InternalUnpair.right (payload.relabel Sum.inl) left).imp
   ((Premises p H G W P left right leftOut rightOut parameter).imp (equal leftOut rightOut))
def atPayload {alpha : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (payload : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (payloadMatrix p H G W P payload)
def payloadPredicate (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 {alpha : Type} : Formula (alpha ⊕ Fin 1) := atPayload p H G W P (.var (.inr 0))
def belowPayload {alpha : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (payload : OTerm alpha) : Formula alpha := InternalStrongInduction.below (payloadPredicate p H G W P) payload
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalInductionDefinitions
