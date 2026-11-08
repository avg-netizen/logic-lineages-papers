module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainCodecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchEvaluationProof
open Source InternalOriginalObjectFiberSourceDispatch
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open InternalCanonicalFixedWindowVertexDispatchEvaluationProof (constantEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local instance] Classical.propDecidable

/-- The original product encoder retains its raw natural second coordinate. -/
theorem objectCodePair (Gamma : List Ty) (payload : Nat) :
    ContextUniform.objectCode Gamma payload = Nat.pair (Encodable.encode Gamma) payload :=
  Encodable.encode_prod_val Gamma payload

/-- The exact original object decoder recognizes the fixed context fiber. -/
theorem objectFiberDecode (Gamma : List Ty) (object : Nat) :
    Encodable.decode (α := ContextUniform.Object) object =
      some (Gamma,(Nat.unpair object).2) ↔
      (Nat.unpair object).1 = Encodable.encode Gamma := by
  rw [JointGammaDomainCodecProof.actualObjectCodec.2.1
    object (Gamma,(Nat.unpair object).2),objectCodePair]
  constructor
  · intro h
    have hu := congrArg (fun code => (Nat.unpair code).1) h
    simpa only [Nat.unpair_pair] using hu.symm
  · intro h
    rw [← h]
    exact Nat.pair_unpair object

theorem projectionEvaluation {n : Nat} (i : Fin n) (xs : List.Vector Nat n) :
    evaluate (.projection i) xs = xs.get i := rfl

theorem actualOriginalObjectSourceAuxiliaryCalibration :
    InternalOriginalObjectFiberSourceDispatchTargets.ActualOriginalObjectSourceAuxiliaryCalibration := by
  refine ⟨?_,?_,?_,?_⟩
  · intro xs
    obtain ⟨obj,hd⟩ := JointGammaDomainCodecProof.actualObjectCodec.1 (xs.get 0)
    have he := (JointGammaDomainCodecProof.actualObjectCodec.2.1 (xs.get 0) obj).mp hd
    rw [objectCodePair] at he
    have hx : xs = xs.get 0 ::ᵥ List.Vector.nil := by
      apply List.Vector.ext
      intro i
      refine Fin.cases ?_ (fun j => Fin.elim0 j) i
      rfl
    change evaluate InternalUnpair.left xs = GammaGuardCalibration.gammaCode (xs.get 0)
    rw [hx,(InternalUnpairEvaluationProof.exactUnpairEvaluation (xs.get 0)).1]
    change (Nat.unpair (xs.get 0)).1 = GammaGuardCalibration.gammaCode (xs.get 0)
    unfold GammaGuardCalibration.gammaCode
    rw [hd]
    simp only [Option.map_some,Option.getD_some]
    rw [← he,Nat.unpair_pair]
  · intro xs
    rw [valid,constantEvaluation]
    obtain ⟨obj,hd⟩ := JointGammaDomainCodecProof.actualObjectCodec.1 (xs.get 0)
    change 1 = match Encodable.decode (α := ContextUniform.Object) (xs.get 0),
      Encodable.decode (α := ContextUniform.Object) (xs.get 0) with
      | some f, some a => (decide (f.1 = a.1)).toNat
      | _, _ => 0
    rw [hd]
    simp
  · intro xs
    rw [tag,leftOfEvaluation,rightOfEvaluation]
    rfl
  · intro xs
    have hx : xs = xs.get 0 ::ᵥ xs.get 1 ::ᵥ List.Vector.nil := by
      apply List.Vector.ext
      intro i
      refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i <;> rfl
    change evaluate InternalListCodec.consCode xs = 1 + Nat.pair (xs.get 0) (xs.get 1)
    rw [hx,InternalListCodecEvaluationProof.consEvaluation]
    rfl

theorem positiveActivationEvaluation (window : Nat) (Gamma : List Ty) (xs : List.Vector Nat 4) :
    evaluate (positiveActivation window Gamma) xs =
      if xs.get 0 = window ∧ ((Nat.unpair (xs.get 1)).1 = Encodable.encode Gamma ∧
        (Nat.unpair (xs.get 2)).1 = Encodable.encode Gamma) then 1 else 0 := by
  simp only [positiveActivation,conjunctionEvaluation,sameEvaluation,leftOfEvaluation,
    constantEvaluation,projectionEvaluation]
  by_cases hc : xs.get 0 = window <;>
    by_cases hf : (Nat.unpair (xs.get 1)).1 = Encodable.encode Gamma <;>
    by_cases ht : (Nat.unpair (xs.get 2)).1 = Encodable.encode Gamma <;> simp [hc,hf,ht]

theorem positiveBranchEvaluation (data : Data) (xs : List.Vector Nat 4) :
    evaluate (positiveBranch data) xs =
      evaluate (InternalPathChecker.checker (InternalCanonicalQuotientEdgeSelection.edgeChecker data) true)
        (List.Vector.ofFn ![(Nat.unpair (xs.get 1)).2,(Nat.unpair (xs.get 2)).2,xs.get 3]) := by
  change evaluate (InternalPathChecker.checker (InternalCanonicalQuotientEdgeSelection.edgeChecker data) true)
    (List.Vector.ofFn fun i : Fin 3 => evaluate
      ((![rightOf (.projection 1),rightOf (.projection 2),.projection 3] : Fin 3 → Program 4) i) xs) = _
  congr 1
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  · exact rightOfEvaluation (.projection 1) xs
  · exact rightOfEvaluation (.projection 2) xs
  · rfl

theorem actualOriginalObjectSourcePositiveEvaluation :
    InternalOriginalObjectFiberSourceDispatchTargets.ActualOriginalObjectSourcePositiveEvaluation := by
  intro window Gamma data oldPositive xs
  refine ⟨positiveActivationEvaluation window Gamma xs,?_⟩
  rw [positive,evalBranch,positiveActivationEvaluation]
  by_cases h : xs.get 0 = window ∧ ((Nat.unpair (xs.get 1)).1 = Encodable.encode Gamma ∧
      (Nat.unpair (xs.get 2)).1 = Encodable.encode Gamma)
  · simp only [h]
    exact positiveBranchEvaluation data xs
  · simp only [h,if_false,if_true]

theorem typedActivationEvaluation (window : Nat) (Gamma : List Ty) (xs : List.Vector Nat 3) :
    evaluate (typedActivation window Gamma) xs =
      if xs.get 0 = window ∧ (Nat.unpair (xs.get 2)).1 = Encodable.encode Gamma then 1 else 0 := by
  simp only [typedActivation,conjunctionEvaluation,sameEvaluation,leftOfEvaluation,
    constantEvaluation,projectionEvaluation]
  by_cases hc : xs.get 0 = window <;>
    by_cases ho : (Nat.unpair (xs.get 2)).1 = Encodable.encode Gamma <;> simp [hc,ho]

theorem typedBranchEvaluation (data : Data) (xs : List.Vector Nat 3) :
    evaluate (typedBranch data) xs = evaluate (InternalCanonicalDescentSelection.selectedTyped data)
      (List.Vector.ofFn ![(Nat.unpair (xs.get 2)).2,xs.get 1]) := by
  change evaluate (InternalCanonicalDescentSelection.selectedTyped data)
    (List.Vector.ofFn fun i : Fin 2 => evaluate
      ((![rightOf (.projection 2),.projection 1] : Fin 2 → Program 3) i) xs) = _
  congr 1
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i
  · exact rightOfEvaluation (.projection 2) xs
  · rfl

theorem actualOriginalObjectSourceTypedEvaluation :
    InternalOriginalObjectFiberSourceDispatchTargets.ActualOriginalObjectSourceTypedEvaluation := by
  intro window Gamma data oldTyped xs
  refine ⟨typedActivationEvaluation window Gamma xs,?_⟩
  rw [typed,evalBranch,typedActivationEvaluation]
  by_cases h : xs.get 0 = window ∧ (Nat.unpair (xs.get 2)).1 = Encodable.encode Gamma
  · simp only [h]
    exact typedBranchEvaluation data xs
  · simp only [h,if_false,if_true]

theorem vertexActivationCompositionEvaluation (window : Nat) (data : Data) (xs : List.Vector Nat 5) :
    evaluate (.composition (InternalCanonicalFixedWindowVertexDispatch.activation window data)
      ![.projection 0,.projection 1,.projection 2,rightOf (.projection 4),rightOf (.projection 3)]) xs =
    evaluate (InternalCanonicalFixedWindowVertexDispatch.activation window data)
      (List.Vector.ofFn ![xs.get 0,xs.get 1,xs.get 2,(Nat.unpair (xs.get 4)).2,(Nat.unpair (xs.get 3)).2]) := by
  change evaluate (InternalCanonicalFixedWindowVertexDispatch.activation window data)
    (List.Vector.ofFn fun i : Fin 5 => evaluate
      ((![.projection 0,.projection 1,.projection 2,rightOf (.projection 4),rightOf (.projection 3)] :
        Fin 5 → Program 5) i) xs) = _
  congr 1
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (fun j => Fin.elim0 j))))) i
  · rfl
  · rfl
  · rfl
  · exact rightOfEvaluation (.projection 4) xs
  · exact rightOfEvaluation (.projection 3) xs

theorem resultActivationEvaluation (window : Nat) (Gamma : List Ty) (data : Data)
    (xs : List.Vector Nat 5) :
    evaluate (resultActivation window Gamma data) xs =
      if resultActive window Gamma data (xs.get 0) (xs.get 1) (xs.get 2) (xs.get 3) (xs.get 4)
        then 1 else 0 := by
  rw [resultActivation,conjunctionEvaluation,sameEvaluation,leftOfEvaluation,constantEvaluation,
    conjunctionEvaluation,sameEvaluation,leftOfEvaluation,constantEvaluation,
    vertexActivationCompositionEvaluation,InternalCanonicalFixedWindowVertexDispatchEvaluationProof.activationEvaluation]
  change (if (if (Nat.unpair (xs.get 3)).1 = Encodable.encode Gamma then 1 else 0) = 1 ∧
    (if (if (Nat.unpair (xs.get 4)).1 = Encodable.encode Gamma then 1 else 0) = 1 ∧
      (if InternalCanonicalFixedWindowVertexDispatch.Active window data (xs.get 0) (xs.get 1)
        (xs.get 2) (Nat.unpair (xs.get 4)).2 (Nat.unpair (xs.get 3)).2 then 1 else 0) = 1
      then 1 else 0) = 1 then 1 else 0) = _
  by_cases hf : (Nat.unpair (xs.get 3)).1 = Encodable.encode Gamma <;>
    by_cases ha : (Nat.unpair (xs.get 4)).1 = Encodable.encode Gamma <;>
    by_cases hv : InternalCanonicalFixedWindowVertexDispatch.Active window data (xs.get 0) (xs.get 1)
      (xs.get 2) (Nat.unpair (xs.get 4)).2 (Nat.unpair (xs.get 3)).2 <;>
    simp [resultActive,hf,ha,hv]

/-- Keep the arbitrary application AST opaque while normalizing its inputs. -/
theorem resultPayloadEvaluation (p : Program 4) (xs : List.Vector Nat 5) :
    evaluate (.composition p
      ![.projection 1,.projection 2,rightOf (.projection 3),rightOf (.projection 4)]) xs =
    evaluate p (List.Vector.ofFn ![xs.get 1,xs.get 2,
      (Nat.unpair (xs.get 3)).2,(Nat.unpair (xs.get 4)).2]) := by
  change evaluate p
    (List.Vector.ofFn fun i : Fin 4 => evaluate
      ((![.projection 1,.projection 2,rightOf (.projection 3),rightOf (.projection 4)] :
        Fin 4 → Program 5) i) xs) = _
  apply congrArg (evaluate p)
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)))) i
  · rfl
  · rfl
  · exact rightOfEvaluation (.projection 3) xs
  · exact rightOfEvaluation (.projection 4) xs

theorem resultBranchEvaluation (Gamma : List Ty) (data : Data) (xs : List.Vector Nat 5) :
    evaluate (resultBranch Gamma data) xs = Nat.pair (Encodable.encode Gamma)
      (evaluate (InternalCanonicalQuotientEdgeApplicationLift.actualJ data)
        (List.Vector.ofFn ![xs.get 1,xs.get 2,(Nat.unpair (xs.get 3)).2,(Nat.unpair (xs.get 4)).2])) := by
  rw [resultBranch,pairOfEvaluation,constantEvaluation]
  exact congrArg (Nat.pair (Encodable.encode Gamma))
    (resultPayloadEvaluation (InternalCanonicalQuotientEdgeApplicationLift.actualJ data) xs)

theorem resultEvaluation (window : Nat) (Gamma : List Ty) (data : Data)
    (oldResult : Program 5) (xs : List.Vector Nat 5) :
    evaluate (result window Gamma data oldResult) xs =
      if resultActive window Gamma data (xs.get 0) (xs.get 1) (xs.get 2) (xs.get 3) (xs.get 4)
      then Nat.pair (Encodable.encode Gamma)
        (evaluate (InternalCanonicalQuotientEdgeApplicationLift.actualJ data)
          (List.Vector.ofFn ![xs.get 1,xs.get 2,(Nat.unpair (xs.get 3)).2,(Nat.unpair (xs.get 4)).2]))
      else evaluate oldResult xs := by
  rw [result,evalBranch,resultActivationEvaluation]
  by_cases h : resultActive window Gamma data (xs.get 0) (xs.get 1) (xs.get 2) (xs.get 3) (xs.get 4)
  · simp only [h]
    exact resultBranchEvaluation Gamma data xs
  · simp only [h,if_false,if_true]

theorem actualOriginalObjectSourceResultEvaluation :
    InternalOriginalObjectFiberSourceDispatchTargets.ActualOriginalObjectSourceResultEvaluation := by
  intro window Gamma data oldResult xs
  have ha := resultActivationEvaluation window Gamma data xs
  have hr := resultEvaluation window Gamma data oldResult xs
  by_cases h : resultActive window Gamma data (xs.get 0) (xs.get 1) (xs.get 2) (xs.get 3) (xs.get 4)
  · have h' := h
    unfold resultActive InternalCanonicalFixedWindowVertexDispatch.Active
      InternalCanonicalFixedWindowVertexDispatch.typedChecker at h'
    rw [if_pos h] at ha hr
    constructor
    · rw [if_pos h']
      exact ha
    · rw [if_pos h']
      exact hr
  · have h' := h
    unfold resultActive InternalCanonicalFixedWindowVertexDispatch.Active
      InternalCanonicalFixedWindowVertexDispatch.typedChecker at h'
    rw [if_neg h] at ha hr
    constructor
    · rw [if_neg h']
      exact ha
    · rw [if_neg h']
      exact hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchEvaluationProof
