module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentCandidate.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary
open InternalOriginalUniformParameterLeaves Source
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership

def countValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 2) : Nat :=
  decodedValue n (fun ctx obj =>
    ((NumberedUniformPackedDecoding.rawPackedDecode n arity obj.1 obj.2).map
      (fun q => (ContextUniformPrimary.vertices arity ctx.1.1 ctx.1.2 obj.1 q).length)).getD 0)
    (v.get 0) (v.get 1)

def poolValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 2) : Nat :=
  decodedValue n (fun ctx obj =>
    ((NumberedUniformPackedDecoding.rawPackedDecode n arity obj.1 obj.2).map
      (fun q => entriesCode (ContextUniformPrimary.vertices arity ctx.1.1 ctx.1.2 obj.1 q))).getD 0)
    (v.get 0) (v.get 1)

def edgeValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 3) : Nat :=
  match Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 2)).1,
      Encodable.decode (α := NumberedUniformPackedDecoding.RawPacked n) (v.get 0),
      Encodable.decode (α := NumberedUniformPackedDecoding.RawPacked n) (v.get 1) with
  | some ctx, some a, some b =>
      (NumberedExchangeCode.packedCodeExchange arity ctx.1.1 ctx.1.2 a b).toNat
  | _, _, _ => 0

def SuppliersCalibrated (n : Nat) (arity : Fin n → Nat)
    (C P : Program 2) (E : Program 3) : Prop :=
  (∀ v, evaluate C v = countValue n arity v) ∧
  (∀ v, evaluate P v = poolValue n arity v) ∧
  (∀ v, evaluate E v = edgeValue n arity v)

/-- Actual original invalid-seed guard and explicit checked reachability run.
Only subordinate count/pool/edge ASTs are selected by PR existence. -/
def primary (T C P : Program 2) (E : Program 3) : Program 2 :=
  InternalAcceptance.branch T (InternalAcceptance.constantZero 2)
    (.composition (PrimaryIteration.run E) ![C,P,.projection 0,.projection 1])
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary
