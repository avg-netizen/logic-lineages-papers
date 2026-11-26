module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open TwoSol20261113.CalibratedPrimary.Membership

theorem zeroEvaluation (E : Program 3) (pool reached parameter : Nat) :
    evaluate (iterate E) (ofFn ![0,pool,reached,parameter]) = reached := rfl

theorem successorEvaluation (E : Program 3) (count pool reached parameter : Nat) :
    evaluate (iterate E) (ofFn ![count+1,pool,reached,parameter]) =
      evaluate (PrimaryExpansion.expand E) (ofFn ![pool,
        evaluate (iterate E) (ofFn ![count,pool,reached,parameter]),parameter]) := rfl

theorem listEncodingTotal (code : Nat) : numbersNumber ((decodeNumbers code).getD []) = code := by
  obtain ⟨xs,hxs⟩ := NumberedMultisetNumericTotalityProof.decoderTotality code
  rw [hxs]
  exact numbersSound code xs hxs

theorem iterationNative : Targets.IterationNative := by
  intro E count pool reached parameter
  induction count with
  | zero =>
    rw [zeroEvaluation]
    exact (listEncodingTotal reached).symm
  | succ count ih =>
    rw [successorEvaluation,ih,PrimaryExpansion.NativeProof.expansionNative,numbersRoundTrip]
    simp only [Option.getD_some,Function.iterate_succ_apply']

theorem originalIteration (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S : List Source.Ty) (E : Program 3) (parameter : Nat)
    (hE : ∀ a r : NumberedUniformPackedDecoding.RawPacked n,
      evaluate E (ofFn ![Encodable.encode a,Encodable.encode r,parameter]) =
        (NumberedExchangeCode.packedCodeExchange arity symbols S a r).toNat)
    (count : Nat) (pool reached : List (NumberedUniformPackedDecoding.RawPacked n)) :
    evaluate (iterate E) (ofFn ![count,entriesCode pool,entriesCode reached,parameter]) =
      entriesCode ((ContextUniformPrimary.step arity symbols S pool)^[count] reached) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [successorEvaluation,ih,
      PrimaryExpansion.NativeProof.originalStepCalibration n arity symbols S E parameter hE,
      Function.iterate_succ_apply']

theorem originalPrimaryCalibration : Targets.OriginalPrimaryCalibration := by
  intro n arity symbols S Gamma E parameter hE q
  let pool := ContextUniformPrimary.vertices arity symbols S Gamma q
  have hs : evaluate (.composition InternalListCodec.consCode
      ![.projection (2 : Fin 4),InternalAcceptance.constantZero 4])
      (ofFn ![pool.length,entriesCode pool,Encodable.encode q,parameter]) = entriesCode [q] := by
    change evaluate InternalListCodec.consCode (Encodable.encode q ::ᵥ 0 ::ᵥ nil) = _
    rw [InternalListCodecEvaluationProof.consEvaluation]
    rfl
  change evaluate (iterate E) (ofFn ![pool.length,entriesCode pool,
    evaluate (.composition InternalListCodec.consCode ![.projection (2 : Fin 4),InternalAcceptance.constantZero 4])
      (ofFn ![pool.length,entriesCode pool,Encodable.encode q,parameter]),parameter]) = _
  rw [hs,originalIteration n arity symbols S E parameter hE]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.NativeProof
