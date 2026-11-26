module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor.NativeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
/-- The literal existing finite dependency cache, with the original pair-node
fuel measure, ordered two children and newly calibrated enumeration combine. -/
def graph (n : Nat) : Program 3 := ExchangeGraphRecursion.graph
  OriginalEnumerationRecursionInterface.R OriginalEnumerationRecursionInterface.D (OriginalEnumerationRecursionInterface.G n)
/-- Existing own-root final cache extraction at actual R(seed)+1. No changed
rank, table encoding, rectangular course-of-values evaluator or selected tuple. -/
def enumeration (n : Nat) : Program 2 := ExchangeSelectedRecursor.exchange
  OriginalEnumerationRecursionInterface.R OriginalEnumerationRecursionInterface.D (OriginalEnumerationRecursionInterface.G n)
/-- Transparent numeric comparator only, not a replacement executable AST.
The parameter is the original nested pair; arbitrary numeric fields retain the
literal layer behavior, including malformed encoded heads and list entries. -/
def numericLayer (n variableBound param prior opened : Nat) : Nat :=
  evaluate (OriginalEnumerationConstructorLayer.layer n) (List.Vector.ofFn ![
    (Nat.unpair param).1,
    (Nat.unpair (Nat.unpair param).2).1,
    (Nat.unpair (Nat.unpair (Nat.unpair param).2).2).1,
    (Nat.unpair (Nat.unpair (Nat.unpair param).2).2).2,
    variableBound,prior,opened])
/-- All-raw comparator with exact original depth convention. At successor the
prior and opened calls both use predecessor fuel, with opened bound+1. -/
def numeric (n : Nat) : Nat → Nat → Nat → Nat
  | 0,_,_ => 0
  | fuel+1,variableBound,param => numericLayer n variableBound param
      (numeric n fuel variableBound param) (numeric n fuel (variableBound+1) param)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion
