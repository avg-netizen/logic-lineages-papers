module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedSortInductionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalAdditionLawsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SortWeightedDefinitions

def fields {k : Nat} (F : Program (k+1)) {alpha : Type}
 (raw sorted sum : OTerm alpha) (params : Fin k → OTerm alpha) : Formula alpha :=
 graph1 OriginalNumericListSort.sort sorted raw ⊓
 programGraph (weighted F) sum (Fin.cons raw params)
def result {k : Nat} (F : Program (k+1)) {alpha : Type}
 (sorted sum : OTerm alpha) (params : Fin k → OTerm alpha) : Formula alpha :=
 programGraph (weighted F) sum (Fin.cons sorted params)
def matrix {k : Nat} (F : Program (k+1)) {alpha : Type}
 (raw : OTerm alpha) (params : Fin k → OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
 (fields F (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
   (fun i => (params i).relabel Sum.inl)).imp
 (result F (.var (.inr 0)) (.var (.inr 1)) (fun i => (params i).relabel Sum.inl))
def AtRaw {k : Nat} (F : Program (k+1)) {alpha : Type}
 (raw : OTerm alpha) (params : Fin k → OTerm alpha) : Formula alpha :=
 InternalClosedPrograms.allBlock (matrix F raw params)
def rawPredicate {k : Nat} (F : Program (k+1)) {alpha : Type}
 (params : Fin k → OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
 AtRaw F (.var (.inr 0)) (fun i => (params i).relabel Sum.inl)
def BelowRaw {k : Nat} (F : Program (k+1)) {alpha : Type}
 (raw : OTerm alpha) (params : Fin k → OTerm alpha) : Formula alpha :=
 InternalStrongInduction.below (rawPredicate F params) raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedSortInductionDefinitions
