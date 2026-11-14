module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontier.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Step inputs [stage index,previous graph,seed,parameter].
The ORIGINAL source-rank is supplied by R, evaluated at the fixed seed. -/
def rank (R : Program 2) : Program 4 := .composition R ![.projection 2,.projection 3]
/-- subtract takes [counter,minuend], hence this is rank(seed)-index. -/
def remaining (R : Program 2) : Program 4 :=
  .composition InternalEqualityTest.subtract ![.projection 0,rank R]
def frontier (R D : Program 2) : Program 4 :=
  .composition (ExchangeFrontier.bindList D) ![remaining R,.projection 2,.projection 3]
def step (R D : Program 2) (G : Program 3) : Program 4 :=
  .composition (ExchangeGraphStage.stage D G) ![frontier R D,.projection 1,.projection 3]
/-- Inputs [stage count,seed,parameter]. Initial graph is empty, and each successor
REPLACES it by the current frontier filterMap using the same previous graph. -/
def graph (R D : Program 2) (G : Program 3) : Program 3 :=
  .recursion (InternalAcceptance.constantZero 2) (step R D G)
def frontierList (d : Nat → Nat → List Nat) (seed param : Nat) : Nat → List Nat :=
  Nat.rec [seed] (fun _ nodes => nodes.flatMap (fun node => d node param))
def graphList (m : Nat → Nat → Nat) (d : Nat → Nat → List Nat)
    (g : Nat → List Nat → Nat → Option Nat) (seed param : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | i+1 => (frontierList d seed param (m seed param - i)).filterMap (fun node =>
      (g node ((d node param).flatMap (fun k => ((graphList m d g seed param i).lookup k).toList)) param).map
        (fun value => (node,value)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion
