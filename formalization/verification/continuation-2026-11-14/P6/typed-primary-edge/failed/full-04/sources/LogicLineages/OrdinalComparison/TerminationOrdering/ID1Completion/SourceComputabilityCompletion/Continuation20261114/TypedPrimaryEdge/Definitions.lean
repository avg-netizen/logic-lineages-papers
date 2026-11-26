module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SeededPrimaryPool.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TypedPrimaryEdge
open Source
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Original raw structural exchange, with all original context/packed decode defaults. -/
def structuralValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 3) : Nat :=
  match Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 2)).1,
      Encodable.decode (α := NumberedUniformPackedDecoding.RawPacked n) (v.get 0),
      Encodable.decode (α := NumberedUniformPackedDecoding.RawPacked n) (v.get 1) with
  | some ctx, some a, some b =>
      (NumberedExchangeCode.codeExchange arity ctx.1.1 ctx.1.2 a.2 b.2).toNat
  | _, _, _ => 0
/-- Actual numeric packed type fields, not an opaque selected type supplier. -/
def typeField (i : Fin 3) : Program 3 := .composition InternalUnpair.left (fun _ : Fin 1 => .projection i)
def typeGuard : Program 3 := .composition InternalEqualityTest.equalityTest ![typeField 0,typeField 1]
def edge (B : Program 3) : Program 3 := InternalAcceptance.conjunction typeGuard B
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TypedPrimaryEdge
