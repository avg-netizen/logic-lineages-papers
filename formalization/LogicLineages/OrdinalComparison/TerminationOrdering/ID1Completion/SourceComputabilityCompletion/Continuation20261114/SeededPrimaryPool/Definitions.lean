module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.LengthAlignedPrimary.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SeededPrimaryPool
open InternalOriginalUniformParameterLeaves Source
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership
/-- Original candidates only, preserving every decode-failure default. -/
def candidatesValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 2) : Nat :=
  decodedValue n (fun ctx obj =>
    ((NumberedUniformPackedDecoding.rawPackedDecode n arity obj.1 obj.2).map
      (fun q => entriesCode (ContextUniformPrimary.candidates arity ctx.1.1 ctx.1.2 obj.1 q))).getD 0)
    (v.get 0) (v.get 1)
/-- Original vertices = decoded seed :: original candidates on admitted inputs;
rejected inputs still produce the original zero code. -/
def pool (T Q : Program 2) : Program 2 :=
  InternalAcceptance.branch T (InternalAcceptance.constantZero 2)
    (.composition InternalListCodec.consCode ![.projection 0,Q])
def primary (T Q : Program 2) (E : Program 3) : Program 2 :=
  LengthAlignedPrimary.primary T (pool T Q) E
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SeededPrimaryPool
