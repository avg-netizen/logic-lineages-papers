module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.CoherenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeNumericSuppliers.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeNumericSuppliers.PrimitiveProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof

theorem extractSingleton (seed value : Nat) :
    evaluate extract (ofFn ![numbersNumber [Nat.pair seed value]]) = value := by
  have hh : evaluate InternalListCodec.headCode (ofFn ![numbersNumber [Nat.pair seed value]]) = Nat.pair seed value := by
    rw [InternalEqualityTestEvaluationProof.vectorOne,InternalListCodecEvaluationProof.headEvaluation]
    simp only [numbersNumber,Nat.add_comm 1,Nat.add_sub_cancel,Nat.unpair_pair]
  change evaluate InternalUnpair.right (ofFn ![evaluate InternalListCodec.headCode _]) = value
  rw [hh,InternalEqualityTestEvaluationProof.vectorOne]
  exact (InternalUnpairEvaluationProof.exactUnpairEvaluation (Nat.pair seed value)).2

theorem nativeFinalValue : Targets.NativeFinalValue := by
  intro R D G m d g f hr hd hg hord hlayer seed param
  have hc : evaluate (count R) (ofFn ![seed,param]) = m seed param + 1 := by
    change Nat.succ (evaluate R (ofFn ![seed,param])) = _
    rw [hr]
  have ht : evaluate (finalGraph R D G) (ofFn ![seed,param]) =
      numbersNumber [Nat.pair seed (f seed param)] := by
    change evaluate (ExchangeGraphRecursion.graph R D G)
      (ofFn ![evaluate (count R) _,seed,param]) = _
    rw [hc]
    have h := ExchangeGraphRecursion.CoherenceProof.nativeCoherentGraph R D G m d g f
      hr hd hg hord hlayer (m seed param+1) seed param (Nat.le_refl _)
    simpa only [Nat.sub_self] using h
  change evaluate extract (ofFn ![evaluate (finalGraph R D G) _]) = _
  rw [ht]
  exact extractSingleton seed (f seed param)

theorem concreteSelection : Targets.ConcreteSelection := by
  intro n arity
  obtain ⟨hpR,hpD,hpG⟩ := ExchangeNumericSuppliers.PrimitiveProof.nativePrimitiveSuppliers n arity
  obtain ⟨R,hR⟩ := Proof.allPrimitiveFunctions 2 _ hpR
  obtain ⟨D,hD⟩ := Proof.allPrimitiveFunctions 2 _ hpD
  obtain ⟨G,hG⟩ := Proof.allPrimitiveFunctions 3 _ hpG
  have hr : ∀ seed param, evaluate R (ofFn ![seed,param]) = ExchangeNumericSuppliers.rankAt n seed param := by
    intro seed param; exact hR _
  have hd : ∀ node param, evaluate D (ofFn ![node,param]) = numbersNumber (ExchangeNumericSuppliers.depsAt n node param) := by
    intro node param; exact hD _
  have hg : ∀ node vals param, evaluate G (ofFn ![node,numbersNumber vals,param]) =
      Encodable.encode (ExchangeNumericSuppliers.layerAt n arity node vals param) := by
    intro node vals param
    rw [hG]
    simp only [ExchangeNumericSuppliers.layerValue,List.Vector.get_ofFn,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,numbersRoundTrip,Option.getD_some]
  have he (seed param : Nat) : evaluate (exchange R D G) (ofFn ![seed,param]) =
      ExchangeNumericSuppliers.valueAt n arity seed param :=
    nativeFinalValue R D G _ _ _ _ hr hd hg
      (ExchangeNumericSuppliers.NativeProof.nativeRankDecrease n)
      (ExchangeNumericSuppliers.NativeProof.nativeLayerLaw n arity) seed param
  refine ⟨R,D,G,hR,hD,hG,?_,?_⟩
  · intro v
    have hvec : v.get = ![v.get 0,v.get 1] := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
    have hv := congrArg List.Vector.ofFn hvec
    rw [List.Vector.ofFn_get] at hv
    rw [hv]
    exact he _ _
  · intro window source target
    rw [he,ExchangeNumericSuppliers.NativeProof.nativeOriginalValue]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor.NativeProof
