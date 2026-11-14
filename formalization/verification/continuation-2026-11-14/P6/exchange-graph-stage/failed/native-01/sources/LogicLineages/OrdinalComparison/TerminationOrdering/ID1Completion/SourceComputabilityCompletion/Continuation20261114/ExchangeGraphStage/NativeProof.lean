module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphStage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphStage.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalAcceptanceCalibrationProof NumberedMultisetNumeric NumberedMultisetNumericSupportProof

theorem coveredMap (keys carrier : List Nat) (f : Nat → Nat)
    (h : ∀ k ∈ keys, k ∈ carrier) :
    keys.flatMap (fun k => ((carrier.map (fun x => (x,f x))).lookup k).toList) = keys.map f := by
  induction keys with
  | nil => rfl
  | cons k keys ih =>
    have hk := h k (List.mem_cons_self)
    have ht : ∀ x ∈ keys, x ∈ carrier := fun x hx => h x (List.mem_cons_of_mem k hx)
    rw [List.flatMap_cons,List.lookup_graph f hk,Option.toList_some,List.cons_append,List.nil_append,ih ht]
    rfl

theorem nativeCoveredMap : Targets.NativeCoveredMap := by
  intro keys carrier f h
  have hm := ExchangeMapGraph.NativeProof.nativeMapGraph (carrier.map (fun k => (k,f k))) keys
  simp only [List.map_map,Function.comp_def] at hm
  rw [hm,coveredMap keys carrier f h]

theorem answerValue (D : Program 2) (G : Program 3)
    (d : Nat → Nat → List Nat) (g : Nat → List Nat → Nat → Option Nat)
    (hd : ∀ node param, evaluate D (ofFn ![node,param]) = numbersNumber (d node param))
    (hg : ∀ node vals param, evaluate G (ofFn ![node,numbersNumber vals,param]) = Encodable.encode (g node vals param))
    (node param : Nat) (old : List (Nat × Nat)) :
    evaluate (nodeAnswer D G) (ofFn ![node,numbersNumber (old.map (fun kv => Nat.pair kv.1 kv.2)),param]) =
      Encodable.encode (g node ((d node param).flatMap (fun k => (old.lookup k).toList)) param) := by
  have hd' : evaluate (dependencies D) (ofFn ![node,numbersNumber (old.map (fun kv => Nat.pair kv.1 kv.2)),param]) =
      numbersNumber (d node param) := hd node param
  have ha : evaluate (answers D) (ofFn ![node,numbersNumber (old.map (fun kv => Nat.pair kv.1 kv.2)),param]) =
      numbersNumber ((d node param).flatMap (fun k => (old.lookup k).toList)) := by
    change evaluate ExchangeMapGraph.mapGraph (ofFn ![evaluate (dependencies D) _,numbersNumber (old.map (fun kv => Nat.pair kv.1 kv.2))]) = _
    rw [hd']
    exact ExchangeMapGraph.NativeProof.nativeMapGraph old (d node param)
  change evaluate G (ofFn ![node,evaluate (answers D) _,param]) = _
  rw [ha]
  exact hg _ _ _

theorem stepValue (D : Program 2) (G : Program 3) (node rest old param : Nat) (v : Option Nat)
    (hv : evaluate (nodeAnswer D G) (ofFn ![node,old,param]) = Encodable.encode v) :
    evaluate (step D G) (node ::ᵥ rest ::ᵥ old ::ᵥ param ::ᵥ nil) =
      match v with
      | none => rest
      | some value => 1 + Nat.pair (Nat.pair node value) rest := by
  have hs : evaluate (stepAnswer D G) (node ::ᵥ rest ::ᵥ old ::ᵥ param ::ᵥ nil) = Encodable.encode v := hv
  rw [step,evalBranch,hs]
  cases v with
  | none => simp only [Encodable.encode_none,ite_true]; rfl
  | some value =>
    have hp : evaluate (.composition InternalEqualityTest.predecessor (fun _ : Fin 1 => stepAnswer D G))
        (node ::ᵥ rest ::ᵥ old ::ᵥ param ::ᵥ nil) = value := by
      change evaluate InternalEqualityTest.predecessor (ofFn ![evaluate (stepAnswer D G) _]) = _
      rw [hs]
      change evaluate InternalEqualityTest.predecessor (ofFn ![value+1]) = value
      rw [InternalEqualityTestEvaluationProof.vectorOne,InternalEqualityTestEvaluationProof.exactPredecessorEvaluation]
      rfl
    have he : evaluate (entry D G) (node ::ᵥ rest ::ᵥ old ::ᵥ param ::ᵥ nil) = Nat.pair node value := by
      change evaluate InternalPairing.pairing (ofFn ![node,evaluate (.composition InternalEqualityTest.predecessor
        (fun _ : Fin 1 => stepAnswer D G)) _]) = _
      rw [hp,InternalEqualityTestEvaluationProof.vectorTwo]
      exact InternalPairingEvaluationProof.exactPairingEvaluation _ _
    simp only [Encodable.encode_some,Encodable.encode_nat,Nat.succ_ne_zero,ite_false]
    change evaluate InternalListCodec.consCode (ofFn ![evaluate (entry D G) _,rest]) = _
    rw [he,InternalEqualityTestEvaluationProof.vectorTwo]
    exact InternalListCodecEvaluationProof.consEvaluation _ _

theorem stageFold (D : Program 2) (G : Program 3)
    (d : Nat → Nat → List Nat) (g : Nat → List Nat → Nat → Option Nat)
    (hd : ∀ node param, evaluate D (ofFn ![node,param]) = numbersNumber (d node param))
    (hg : ∀ node vals param, evaluate G (ofFn ![node,numbersNumber vals,param]) = Encodable.encode (g node vals param))
    (frontier : List Nat) (old : List (Nat × Nat)) (param : Nat) :
    frontier.foldr (fun node rest => evaluate (step D G)
      (node ::ᵥ rest ::ᵥ numbersNumber (old.map (fun kv => Nat.pair kv.1 kv.2)) ::ᵥ param ::ᵥ nil)) 0 =
    numbersNumber (frontier.filterMap (fun node =>
      (g node ((d node param).flatMap (fun k => (old.lookup k).toList)) param).map (fun value => Nat.pair node value))) := by
  induction frontier with
  | nil => rfl
  | cons node frontier ih =>
    rw [List.foldr_cons,stepValue D G _ _ _ _ _ (answerValue D G d g hd hg node param old),ih,List.filterMap_cons]
    cases h : g node ((d node param).flatMap (fun k => (old.lookup k).toList)) param <;>
      simp only [Option.map_none,Option.map_some,numbersNumber]

theorem nativeStage : Targets.NativeStage := by
  intro D G d g hd hg frontier old param
  have h := InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation
    2 (InternalAcceptance.constantZero 2) (step D G)
    (numbersNumber (old.map (fun kv => Nat.pair kv.1 kv.2)) ::ᵥ param ::ᵥ nil) (numbersNumber frontier)
  change evaluate (stage D G) (ofFn ![numbersNumber frontier,numbersNumber (old.map (fun kv => Nat.pair kv.1 kv.2)),param]) = _ at h
  rw [h,numbersRoundTrip]
  exact stageFold D G d g hd hg frontier old param
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphStage.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphStage.NativeProof
