module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepCheckerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationStepGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRawParserSoundnessSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepCheckerEvaluationProof
open Source NumberedNumericDecoding NumberedNumericCarrier NumberedNumericStep
open NumberedAuxiliaryCoding ApplicationCertificateLift
open InternalApplicationStepPeel InternalApplicationStepChecker
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationProof InternalApplicationStepPeelEvaluationSelectorSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

 theorem endpointIdentity (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (v : List.Vector Nat 5) (k : Nat)
    (h : endpointValue n arity symbols S Gamma v = 1) :
    numericStepTest n arity symbols S Gamma table
      (rawApplication (v.get 0) (v.get 1) (v.get 2) (v.get 4))
      (rawApplication (v.get 0) (v.get 1) (v.get 3) (v.get 4)) (liftStep k) =
    numericStepTest n arity symbols S Gamma table (v.get 2) (v.get 3) k := by
  unfold endpointValue at h
  cases hd : decodeType (v.get 0) with
  | none => simp only [hd, Nat.zero_ne_one] at h
  | some sigma =>
    cases he : decodeType (v.get 1) with
    | none => simp only [hd,he, Nat.zero_ne_one] at h
    | some tau =>
      cases hq : decodeUniverse n arity symbols S Gamma (v.get 2) with
      | none => simp only [hd,he,hq, Nat.zero_ne_one] at h
      | some q =>
        cases hr : decodePackedNumber n arity Gamma (v.get 3) with
        | none => simp only [hd,he,hq,hr, Nat.zero_ne_one] at h
        | some r =>
          cases ha : decodeUniverse n arity symbols S Gamma (v.get 4) with
          | none => simp only [hd,he,hq,hr,ha, Nat.zero_ne_one] at h
          | some a =>
            have hh : q.1 = .arrow sigma tau ∧ r.1 = .arrow sigma tau ∧
                a.1 = sigma ∧ tau ∈ S := by
              simp only [hd,he,hq,hr,ha] at h
              simpa using h
            rcases q with ⟨qt,q⟩
            rcases r with ⟨rt,r⟩
            rcases a with ⟨aty,a⟩
            rcases hh with ⟨hqt,hrt,hat,ht⟩
            dsimp only at hqt hrt hat
            subst qt rt aty
            rw [← NumberedRawParserSoundnessSupportProof.decodedType _ _ hd,
              ← NumberedRawParserSoundnessSupportProof.decodedType _ _ he]
            exact ApplicationStepGuardProof.actualRawEndpointIdentity n arity symbols S Gamma
              table sigma tau q r a _ _ _ k hq hr ha ht

 theorem sourceReconstruction (state : Nat) (h : shape (view state) = true) :
    rawApplication (view state).domain (view state).sourceType
      ((endpointInputs (view state)).get 2) ((endpointInputs (view state)).get 4) =
      (view state).source := by
  have hh : (view state).sourceTag = 2 := (of_decide_eq_true h).2.2.1
  simp only [endpointInputs,List.Vector.get_ofFn,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,
    rawApplication,Nat.unpair_pair]
  rw [← hh]
  simp only [view,Nat.pair_unpair]

 theorem targetReconstruction (state : Nat) (h : shape (view state) = true) :
    rawApplication (view state).domain (view state).sourceType
      ((endpointInputs (view state)).get 3) ((endpointInputs (view state)).get 4) =
      (view state).target := by
  have hh : (view state).path ≠ 0 ∧ (view state).pathHead = 2 ∧
      (view state).sourceTag = 2 ∧ (view state).targetTag = 2 ∧
      (view state).sourceType = (view state).targetType ∧
      (view state).domain = (view state).targetDomain ∧
      (view state).argumentPayload = (view state).targetArgumentPayload := of_decide_eq_true h
  simp only [endpointInputs,List.Vector.get_ofFn,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,
    rawApplication,Nat.unpair_pair]
  rw [← hh.2.2.2.1,hh.2.2.2.2.1,hh.2.2.2.2.2.1,hh.2.2.2.2.2.2]
  simp only [view,Nat.pair_unpair]

 theorem certificateReconstruction (state : Nat) (h : shape (view state) = true) :
    liftStep (Nat.pair (view state).pathTail (view state).payload) =
      (view state).certificate := by
  have hn : (view state).path ≠ 0 := (of_decide_eq_true h).1
  have hh : (view state).pathHead = 2 := (of_decide_eq_true h).2.1
  have hp : 1 + Nat.pair 2 (view state).pathTail = (view state).path := by
    rw [← hh]
    change 1 + Nat.pair (Nat.unpair ((view state).path - 1)).1
      (Nat.unpair ((view state).path - 1)).2 = _
    rw [Nat.pair_unpair]
    omega
  simp only [liftStep,Nat.unpair_pair]
  change Nat.pair (1 + Nat.pair 2 (view state).pathTail) (view state).payload = _
  rw [hp]
  exact Nat.pair_unpair _

 def stateTest (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (state : Nat) : Bool :=
  numericStepTest n arity symbols S Gamma table
    (view state).source (view state).target (view state).certificate

 theorem transitionPreserves (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (endpoint : Program 5) (calibrated : EndpointCalibrated n arity symbols S Gamma endpoint)
    (state : Nat) :
    stateTest n arity symbols S Gamma table
      (evaluate (transition endpoint) (List.Vector.ofFn ![state])) =
    stateTest n arity symbols S Gamma table state := by
  rw [(actualOriginalTransitionCalibration n arity symbols S Gamma endpoint calibrated state).2]
  unfold transitionValue
  split
  next h =>
    have hg : shape (view state) = true ∧
        endpointValue n arity symbols S Gamma (endpointInputs (view state)) = 1 := by
      simpa [guardValue] using h
    have hi := endpointIdentity n arity symbols S Gamma table (endpointInputs (view state))
      (Nat.pair (view state).pathTail (view state).payload) hg.2
    change numericStepTest n arity symbols S Gamma table
      (rawApplication (view state).domain (view state).sourceType
        ((endpointInputs (view state)).get 2) ((endpointInputs (view state)).get 4))
      (rawApplication (view state).domain (view state).sourceType
        ((endpointInputs (view state)).get 3) ((endpointInputs (view state)).get 4))
      (liftStep (Nat.pair (view state).pathTail (view state).payload)) = _ at hi
    rw [sourceReconstruction state hg.1,targetReconstruction state hg.1,
      certificateReconstruction state hg.1] at hi
    simpa only [stateTest,peeledValue,view,Nat.unpair_pair] using hi.symm
  next => rfl

 theorem repeatPreserves (p : Program 1) (f : Nat → Bool)
    (hp : ∀ s, f (evaluate p (List.Vector.ofFn ![s])) = f s) (code state : Nat) :
    f (evaluate (InternalRawListRepeat.repeatProgram p)
      (code ::ᵥ state ::ᵥ List.Vector.nil)) = f state := by
  rw [InternalRawListRepeat.repeatProgram,
    InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation]
  change f (((NumberedMultisetNumeric.decodeNumbers code).getD []).foldr
    (fun _ result => evaluate p (List.Vector.ofFn ![result])) state) = f state
  generalize (NumberedMultisetNumeric.decodeNumbers code).getD [] = xs
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [List.foldr_cons,hp] using ih

 theorem normalizerPreserves (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (endpoint : Program 5) (calibrated : EndpointCalibrated n arity symbols S Gamma endpoint)
    (state : Nat) :
    stateTest n arity symbols S Gamma table
      (evaluate (normalizer endpoint) (List.Vector.ofFn ![state])) =
    stateTest n arity symbols S Gamma table state := by
  change stateTest n arity symbols S Gamma table
    (evaluate (InternalRawListRepeat.repeatProgram (transition endpoint))
      (List.Vector.ofFn fun i : Fin 2 => evaluate
        ((![rawPath,.projection 0] : Fin 2 → Program 1) i) (List.Vector.ofFn ![state]))) = _
  rw [InternalEqualityTestEvaluationProof.vectorTwo]
  exact repeatPreserves _ _ (transitionPreserves n arity symbols S Gamma table endpoint calibrated) _ state

 theorem actualOriginalCheckerCalibration :
    InternalApplicationStepCheckerTargets.ActualOriginalCheckerCalibration := by
  intro n arity symbols S Gamma table endpoint oldChecker he ho v
  let state := evaluate edgeCode v
  let normalized := evaluate (normalizer endpoint) (List.Vector.ofFn ![state])
  change evaluate oldChecker (List.Vector.ofFn fun i : Fin 3 =>
    evaluate ((![source,target,step] : Fin 3 → Program 1) i)
      (List.Vector.ofFn ![normalized])) = _
  rw [ho]
  change (numericStepTest n arity symbols S Gamma table
    (evaluate source (List.Vector.ofFn ![normalized]))
    (evaluate target (List.Vector.ofFn ![normalized]))
    (evaluate step (List.Vector.ofFn ![normalized]))).toNat = _
  rw [sourceViewEvaluation,targetViewEvaluation,stepViewEvaluation]
  change (stateTest n arity symbols S Gamma table normalized).toNat = _
  rw [normalizerPreserves n arity symbols S Gamma table endpoint he state]
  dsimp [state]
  rw [edgeCodeEvaluation]
  simp only [stateTest,NumberedNumericQuotientEdge.edgeCertificateNumber,view,Nat.unpair_pair]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepCheckerEvaluationProof
