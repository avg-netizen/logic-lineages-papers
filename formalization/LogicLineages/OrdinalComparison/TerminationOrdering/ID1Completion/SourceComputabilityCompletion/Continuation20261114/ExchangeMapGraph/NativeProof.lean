module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalAcceptanceCalibrationProof NumberedMultisetNumeric NumberedMultisetNumericSupportProof

theorem stepLookup (k v rest key : Nat) :
    evaluate lookupStep (Nat.pair k v ::ᵥ rest ::ᵥ key ::ᵥ nil) =
      if k = key then v+1 else rest := by
  have hl : evaluate entryKey (Nat.pair k v ::ᵥ rest ::ᵥ key ::ᵥ nil) = k := by
    change evaluate InternalUnpair.left (ofFn ![Nat.pair k v]) = k
    rw [InternalEqualityTestEvaluationProof.vectorOne]
    simpa only [Nat.unpair_pair,Matrix.cons_val_zero] using (InternalUnpairEvaluationProof.exactUnpairEvaluation (Nat.pair k v)).1
  have hr : evaluate entryValue (Nat.pair k v ::ᵥ rest ::ᵥ key ::ᵥ nil) = v := by
    change evaluate InternalUnpair.right (ofFn ![Nat.pair k v]) = v
    rw [InternalEqualityTestEvaluationProof.vectorOne]
    simpa only [Nat.unpair_pair,Matrix.cons_val_zero] using (InternalUnpairEvaluationProof.exactUnpairEvaluation (Nat.pair k v)).2
  have he : evaluate (.composition InternalEqualityTest.equalityTest ![entryKey,.projection 2])
      (Nat.pair k v ::ᵥ rest ::ᵥ key ::ᵥ nil) = if k = key then 1 else 0 := by
    change evaluate InternalEqualityTest.equalityTest (ofFn ![evaluate entryKey _,key]) = _
    rw [hl,InternalEqualityTestEvaluationProof.vectorTwo]
    exact InternalEqualityTestEvaluationProof.exactEqualityEvaluation _ _
  rw [lookupStep,evalBranch,he]
  change (if (if k = key then 1 else 0) = 0 then rest else Nat.succ (evaluate entryValue _)) = _
  rw [hr]
  by_cases h : k = key <;> simp [h]

theorem lookupFold (entries : List (Nat × Nat)) (key : Nat) :
    (entries.map (fun p => Nat.pair p.1 p.2)).foldr
      (fun a rest => evaluate lookupStep (a ::ᵥ rest ::ᵥ key ::ᵥ nil)) 0 =
      Encodable.encode (entries.lookup key) := by
  induction entries with
  | nil => rfl
  | cons p entries ih =>
    rcases p with ⟨k,v⟩
    rw [List.map_cons,List.foldr_cons,stepLookup,ih]
    by_cases h : k = key
    · subst k; simp [List.lookup_cons]
    · have hn : key ≠ k := Ne.symm h
      have hb : (key == k) = false := beq_false_of_ne hn
      simp [List.lookup_cons,h,hb]

theorem nativeLookup : Targets.NativeLookup := by
  intro entries key
  have h := InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation
    1 (InternalAcceptance.constantZero 1) lookupStep (key ::ᵥ nil)
      (numbersNumber (entries.map (fun p => Nat.pair p.1 p.2)))
  change evaluate lookup (ofFn ![numbersNumber (entries.map (fun p => Nat.pair p.1 p.2)),key]) = _ at h
  rw [h,numbersRoundTrip]
  exact lookupFold entries key

theorem stepMap (entries : List (Nat × Nat)) (key rest : Nat) :
    evaluate mapStep (key ::ᵥ rest ::ᵥ numbersNumber (entries.map (fun p => Nat.pair p.1 p.2)) ::ᵥ nil) =
      match entries.lookup key with
      | none => rest
      | some value => 1 + Nat.pair value rest := by
  have hf : evaluate found (key ::ᵥ rest ::ᵥ numbersNumber (entries.map (fun p => Nat.pair p.1 p.2)) ::ᵥ nil) =
      Encodable.encode (entries.lookup key) := nativeLookup entries key
  rw [mapStep,evalBranch,hf]
  cases ho : entries.lookup key with
  | none => simp only [ho,Encodable.encode_none,ite_true]; rfl
  | some value =>
    have hp : evaluate (.composition InternalEqualityTest.predecessor (fun _ : Fin 1 => found))
        (key ::ᵥ rest ::ᵥ numbersNumber (entries.map (fun p => Nat.pair p.1 p.2)) ::ᵥ nil) = value := by
      change evaluate InternalEqualityTest.predecessor (ofFn ![evaluate found _]) = value
      rw [hf,ho]
      change evaluate InternalEqualityTest.predecessor (ofFn ![value+1]) = value
      rw [InternalEqualityTestEvaluationProof.vectorOne,InternalEqualityTestEvaluationProof.exactPredecessorEvaluation]
      rfl
    simp only [ho,Encodable.encode_some,Encodable.encode_nat,Nat.succ_ne_zero,ite_false]
    change evaluate InternalListCodec.consCode (ofFn ![evaluate (.composition InternalEqualityTest.predecessor
      (fun _ : Fin 1 => found)) _,rest]) = _
    rw [hp,InternalEqualityTestEvaluationProof.vectorTwo]
    exact InternalListCodecEvaluationProof.consEvaluation value rest

theorem mapFold (entries : List (Nat × Nat)) (keys : List Nat) :
    keys.foldr (fun key rest => evaluate mapStep
      (key ::ᵥ rest ::ᵥ numbersNumber (entries.map (fun p => Nat.pair p.1 p.2)) ::ᵥ nil)) 0 =
    numbersNumber (keys.flatMap (fun key => (entries.lookup key).toList)) := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
    rw [List.foldr_cons,stepMap,ih,List.flatMap_cons]
    cases ho : entries.lookup key <;> simp only [ho,Option.toList_none,Option.toList_some,List.nil_append,List.cons_append,numbersNumber]

theorem nativeMapGraph : Targets.NativeMapGraph := by
  intro entries keys
  have h := InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation
    1 (InternalAcceptance.constantZero 1) mapStep
    (numbersNumber (entries.map (fun p => Nat.pair p.1 p.2)) ::ᵥ nil) (numbersNumber keys)
  change evaluate mapGraph (ofFn ![numbersNumber keys,numbersNumber (entries.map (fun p => Nat.pair p.1 p.2))]) = _ at h
  rw [h,numbersRoundTrip]
  exact mapFold entries keys
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph.NativeProof
