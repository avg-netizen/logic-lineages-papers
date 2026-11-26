module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeNumericSuppliers.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def count (R : Program 2) : Program 2 := .composition .succ (fun _ : Fin 1 => R)
def finalGraph (R D : Program 2) (G : Program 3) : Program 2 :=
  .composition (ExchangeGraphRecursion.graph R D G) ![count R,.projection 0,.projection 1]
/-- On the proved final singleton graph, head followed by pair-snd is the exact
nat_omega_rec extraction of index0/snd. On arbitrary codes this AST has its own
explicit codec defaults; no optional-none behavior is silently asserted. -/
def extract : Program 1 := .composition InternalUnpair.right
  (fun _ : Fin 1 => InternalListCodec.headCode)
def exchange (R D : Program 2) (G : Program 3) : Program 2 :=
  .composition extract (fun _ : Fin 1 => finalGraph R D G)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor
