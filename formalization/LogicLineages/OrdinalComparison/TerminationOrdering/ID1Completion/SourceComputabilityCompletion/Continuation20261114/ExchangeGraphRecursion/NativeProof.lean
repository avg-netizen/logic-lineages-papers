module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontier.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphStage.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof

theorem remainingValue (R : Program 2) (i old seed param rankValue : Nat)
    (hr : evaluate R (ofFn ![seed,param]) = rankValue) :
    evaluate (remaining R) (i ::ᵥ old ::ᵥ seed ::ᵥ param ::ᵥ nil) = rankValue - i := by
  change evaluate InternalEqualityTest.subtract (ofFn ![i,evaluate R (ofFn ![seed,param])]) = _
  rw [hr,InternalEqualityTestEvaluationProof.vectorTwo]
  exact InternalEqualityTestEvaluationProof.exactSubtractionEvaluation _ _

theorem stepValue (R D : Program 2) (G : Program 3)
    (m : Nat → Nat → Nat) (d : Nat → Nat → List Nat)
    (g : Nat → List Nat → Nat → Option Nat)
    (hr : ∀ seed param, evaluate R (ofFn ![seed,param]) = m seed param)
    (hd : ∀ node param, evaluate D (ofFn ![node,param]) = numbersNumber (d node param))
    (hg : ∀ node vals param, evaluate G (ofFn ![node,numbersNumber vals,param]) = Encodable.encode (g node vals param))
    (i seed param : Nat) (old : List (Nat × Nat)) :
    evaluate (step R D G) (i ::ᵥ numbersNumber (old.map (fun kv => Nat.pair kv.1 kv.2)) ::ᵥ seed ::ᵥ param ::ᵥ nil) =
    numbersNumber (((frontierList d seed param (m seed param - i)).filterMap (fun node =>
      (g node ((d node param).flatMap (fun k => (old.lookup k).toList)) param).map
        (fun value => Nat.pair node value)))) := by
  have hf : evaluate (frontier R D)
      (i ::ᵥ numbersNumber (old.map (fun kv => Nat.pair kv.1 kv.2)) ::ᵥ seed ::ᵥ param ::ᵥ nil) =
      numbersNumber (frontierList d seed param (m seed param - i)) := by
    change evaluate (ExchangeFrontier.bindList D) (ofFn ![evaluate (remaining R) _,seed,param]) = _
    rw [remainingValue R _ _ _ _ _ (hr seed param)]
    exact ExchangeFrontier.NativeProof.nativeBindList D d hd _ _ _
  change evaluate (ExchangeGraphStage.stage D G)
    (ofFn ![evaluate (frontier R D) _,numbersNumber (old.map (fun kv => Nat.pair kv.1 kv.2)),param]) = _
  rw [hf]
  exact ExchangeGraphStage.NativeProof.nativeStage D G d g hd hg _ old param

theorem successorEvaluation (R D : Program 2) (G : Program 3) (i seed param : Nat) :
    evaluate (graph R D G) (ofFn ![i+1,seed,param]) =
      evaluate (step R D G) (i ::ᵥ evaluate (graph R D G) (ofFn ![i,seed,param]) ::ᵥ seed ::ᵥ param ::ᵥ nil) := rfl

theorem nativeGraph : Targets.NativeGraph := by
  intro R D G m d g hr hd hg i seed param
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [successorEvaluation,ih,stepValue R D G m d g hr hd hg]
    simp only [graphList,List.map_filterMap,Function.comp_def,Option.map_map]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.NativeProof
