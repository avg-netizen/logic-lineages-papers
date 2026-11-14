module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership
/-- Auxiliary potential only. Inputs [head,tail-count,reached]. If this pool
entry is reached, keep tail-count; otherwise count this occurrence. -/
def countStep : Program 3 :=
  InternalAcceptance.branch
    (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize
      (.composition contains ![.projection 2,.projection 0]))
    (.composition .succ (fun _ : Fin 1 => .projection 1)) (.projection 1)
/-- Inputs [pool,reached]. Counts every unreached occurrence in the original
pool. No deduplication, new enumeration, or replacement cutoff. -/
def count : Program 2 :=
  InternalRawListRecursion.listRec (InternalAcceptance.constantZero 1) countStep
/-- Ordinary non-strict arithmetic order, not a semantic/custom relation. -/
def bounded {alpha : Type} (small large : OTerm alpha) : Formula alpha :=
  arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula small large) ⊔
    InternalTagArithmeticSyntaxProof.eqn small large
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount
