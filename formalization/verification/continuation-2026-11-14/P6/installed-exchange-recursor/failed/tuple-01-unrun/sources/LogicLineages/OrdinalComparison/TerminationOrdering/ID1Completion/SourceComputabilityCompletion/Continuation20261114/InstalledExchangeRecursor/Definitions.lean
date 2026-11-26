module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TypedPrimaryEdge.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def validValue (n : Nat) (v : List.Vector Nat 3) : Nat :=
  match Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 2)).1,
      Encodable.decode (α := NumberedUniformPackedDecoding.RawPacked n) (v.get 0),
      Encodable.decode (α := NumberedUniformPackedDecoding.RawPacked n) (v.get 1) with
  | some _, some _, some _ => 1
  | _, _, _ => 0
def windowValue (n : Nat) (v : List.Vector Nat 1) : Nat :=
  ((Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 0)).1).map
    (fun ctx => Encodable.encode ctx.1)).getD 0
def codeField (i : Fin 3) : Program 3 :=
  .composition InternalUnpair.right (fun _ : Fin 1 => .projection i)
def nodeCode : Program 3 := .composition InternalPairing.pairing ![codeField 0,codeField 1]
def windowCode (K : Program 1) : Program 3 := .composition K (fun _ : Fin 1 => .projection 2)
def structural (R D : Program 2) (J V : Program 3) (K : Program 1) : Program 3 :=
  InternalAcceptance.branch V (InternalAcceptance.constantZero 3)
    (.composition (ExchangeSelectedRecursor.exchange R D J) ![nodeCode,windowCode K])
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor
