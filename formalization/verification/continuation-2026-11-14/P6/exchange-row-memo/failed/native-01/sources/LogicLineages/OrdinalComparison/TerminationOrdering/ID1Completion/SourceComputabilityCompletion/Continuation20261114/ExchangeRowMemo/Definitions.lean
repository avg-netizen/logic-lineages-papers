module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeRowMemo
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Rows are indexed by the ORIGINAL source-code rank. The two unchanged
parameters are the window code and original target-code bound. No paired-rank
recursion replaces the source nat_omega_rec. B and R are explicit suppliers,
not alleged implementations of the remaining structural exchange recurrence. -/
def base (B : Program 2) : Program 2 :=
  .composition InternalListCodec.consCode ![B,InternalAcceptance.constantZero 2]
/-- R receives [preceding source rank, complete prior row table,window,bound]. -/
def step (R : Program 4) : Program 4 :=
  .composition InternalListCodec.consCode ![R,.projection 1]
def table (B : Program 2) (R : Program 4) : Program 3 := .recursion (base B) (step R)
def row (B : Program 2) (R : Program 4) : Program 3 :=
  .composition InternalListCodec.headCode (fun _ : Fin 1 => table B R)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeRowMemo
