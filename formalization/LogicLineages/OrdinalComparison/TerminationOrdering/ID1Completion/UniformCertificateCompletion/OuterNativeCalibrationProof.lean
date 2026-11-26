module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterNativeCalibrationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.DecodedSourceCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineRepresentativeEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomParameterEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomRepresentativeEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterNativeCalibrationProof
open Source SourceComputabilityCompletion
open InternalOriginalUniformDescentSelection (Data)
open InternalOriginalUniformParameterLeaves (parameterObject)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- Use the already normalized readyData conclusion exactly once. -/
theorem actualOriginalOuterSelectedDataCalibration :
    OuterNativeCalibrationTargets.ActualOriginalOuterSelectedDataCalibration := by
  intro n arity base window hc hw
  have hs := SpineRepresentativeEvaluationProof.actualOriginalSpineRepresentativeCalibration
    n arity base window hc hw
  have hp := BottomParameterEvaluationProof.actualOriginalBottomParameterCalibration
    n arity (SpineRepresentative.baseData base window) hs
  exact (BottomRepresentativeEvaluationProof.actualOriginalBottomRepresentativeCalibration
    n arity (BottomParameter.baseData (SpineRepresentative.baseData base window)) window hp hw).2

theorem parameterEvaluation {m : Nat} (context object : Program m) (v : List.Vector Nat m) :
    evaluate (Outer.parameter context object) v =
      Nat.pair (evaluate context v) (Nat.unpair (evaluate object v)).1 := by
  rw [Outer.parameter,pairOfEvaluation,leftOfEvaluation]

theorem windowAtEvaluation {m : Nat} (window : Program 1) (context : Fin m)
    (v : List.Vector Nat m) :
    evaluate (Outer.windowAt window context) v =
      evaluate window (ofFn ![v.get context]) := rfl

theorem scalarBranchEvaluation (rawScalar : Program 2) (v : List.Vector Nat 2) :
    evaluate (Outer.scalarBranch rawScalar) v = evaluate rawScalar
      (ofFn ![(Nat.unpair (v.get 1)).2,Nat.pair (v.get 0) (Nat.unpair (v.get 1)).1]) := by
  change evaluate rawScalar (ofFn fun i : Fin 2 => evaluate
    ((Fin.cons (rightOf (.projection 1))
      (Fin.cons (Outer.parameter (.projection 0) (.projection 1)) Fin.elim0) :
        Fin 2 → Program 2) i) v) = _
  congr 1
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i
  · exact rightOfEvaluation (.projection 1) v
  · exact parameterEvaluation (.projection 0) (.projection 1) v

theorem typedBranchEvaluation (data : Data) (v : List.Vector Nat 3) :
    evaluate (Outer.typedBranch data) v =
      evaluate (InternalOriginalUniformDescentSelection.selectedTyped data)
        (ofFn ![(Nat.unpair (v.get 2)).2,v.get 1,
          Nat.pair (v.get 0) (Nat.unpair (v.get 2)).1]) := by
  change evaluate (InternalOriginalUniformDescentSelection.selectedTyped data)
    (ofFn fun i : Fin 3 => evaluate
      ((Fin.cons (rightOf (.projection 2)) (Fin.cons (.projection 1)
        (Fin.cons (Outer.parameter (.projection 0) (.projection 2)) Fin.elim0)) :
          Fin 3 → Program 3) i) v) = _
  congr 1
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  · exact rightOfEvaluation (.projection 2) v
  · rfl
  · exact parameterEvaluation (.projection 0) (.projection 2) v

/-- The parameter slice decodes the ORIGINAL supplied object, not a new
encoding of the raw Context. Pair/unpair is used only on the Object code. -/
theorem objectDecodeAt (context object : Nat) (Gamma : List Ty)
    (hs : ∀ value : Nat,
      parameterObject value (Nat.pair context (Nat.unpair object).1) = some (Gamma,value)) :
    Encodable.decode (α := ContextUniform.Object) object =
      some (Gamma,(Nat.unpair object).2) := by
  simpa only [parameterObject,Nat.unpair_pair,Nat.pair_unpair] using
    hs (Nat.unpair object).2

theorem scalarBranchCalibration (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (v : List.Vector Nat 2) (hw : GuardCalibration.validWindow n (v.get 0) = 1) :
    evaluate (Outer.scalarBranch (RawScalar.checker data)) v =
      ContextUniform.scalarValue n arity v := by
  obtain ⟨ctx,hctx,hS⟩ := (GuardCalibrationProof.actualValidWindowCalibration n (v.get 0)).1.mp hw
  have hp : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair (Nat.pair (v.get 0) (Nat.unpair (v.get 1)).1)).1 = some ctx := by
    simpa only [Nat.unpair_pair] using hctx
  obtain ⟨Gamma,hs⟩ := DecodedSourceCalibrationProof.actualDecodedCompositeCalibration
    n arity data hc (Nat.pair (v.get 0) (Nat.unpair (v.get 1)).1) ctx hp hS
  have ho := objectDecodeAt (v.get 0) (v.get 1) Gamma hs.objectSlice
  rw [scalarBranchEvaluation,hs.scalar]
  simp only [ContextUniform.scalarValue,ho,OrdinaryArithmeticCarrier.scalarValue,
    List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,hctx,Option.any_some]

theorem typedBranchCalibration (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (v : List.Vector Nat 3) (hw : GuardCalibration.validWindow n (v.get 0) = 1) :
    evaluate (Outer.typedBranch data) v = JointGammaTyped.typedValue n arity v := by
  obtain ⟨ctx,hctx,hS⟩ := (GuardCalibrationProof.actualValidWindowCalibration n (v.get 0)).1.mp hw
  have hp : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair (Nat.pair (v.get 0) (Nat.unpair (v.get 2)).1)).1 = some ctx := by
    simpa only [Nat.unpair_pair] using hctx
  obtain ⟨Gamma,hs⟩ := DecodedSourceCalibrationProof.actualDecodedCompositeCalibration
    n arity data hc (Nat.pair (v.get 0) (Nat.unpair (v.get 2)).1) ctx hp hS
  have ho := objectDecodeAt (v.get 0) (v.get 2) Gamma hs.objectSlice
  rw [typedBranchEvaluation,hs.typed]
  simp only [JointGammaTyped.typedValue,ho,OrdinaryArithmeticTypedCarrier.typedValue,
    InternalOriginalTypedCarrier.typedValue,List.Vector.get_ofFn,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,hctx,Option.any_some]
  rfl

theorem validWindowOneOfNonzero (n context : Nat)
    (h : GuardCalibration.validWindow n context ≠ 0) :
    GuardCalibration.validWindow n context = 1 := by
  apply (GuardCalibrationProof.actualValidWindowCalibration n context).1.mpr
  by_contra hn
  exact h ((GuardCalibrationProof.actualValidWindowCalibration n context).2.mpr hn)

/-- All arbitrary input vectors are retained on both sides of the dispatcher. -/
theorem scalarCalibration (n : Nat) (arity : Fin n → Nat) (data : Data)
    (window : Program 1) (oldScalar : Program 2)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (hw : Path.windowCalibrated n window)
    (hold : ∀ v, evaluate oldScalar v = ContextUniform.scalarValue n arity v)
    (v : List.Vector Nat 2) :
    evaluate (Outer.scalar (RawScalar.checker data) window oldScalar) v =
      ContextUniform.scalarValue n arity v := by
  rw [Outer.scalar,evalBranch,windowAtEvaluation]
  by_cases hz : evaluate window (ofFn ![v.get 0]) = 0
  · rw [if_pos hz]
    exact hold v
  · rw [if_neg hz]
    have hn : GuardCalibration.validWindow n (v.get 0) ≠ 0 := by
      intro hzero
      exact hz ((hw (ofFn ![v.get 0])).trans hzero)
    exact scalarBranchCalibration n arity data hc v (validWindowOneOfNonzero n (v.get 0) hn)

theorem typedCalibration (n : Nat) (arity : Fin n → Nat) (data : Data)
    (window : Program 1) (oldTyped : Program 3)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (hw : Path.windowCalibrated n window)
    (hold : ∀ v, evaluate oldTyped v = JointGammaTyped.typedValue n arity v)
    (v : List.Vector Nat 3) :
    evaluate (Outer.typed data window oldTyped) v = JointGammaTyped.typedValue n arity v := by
  rw [Outer.typed,evalBranch,windowAtEvaluation]
  by_cases hz : evaluate window (ofFn ![v.get 0]) = 0
  · rw [if_pos hz]
    exact hold v
  · rw [if_neg hz]
    have hn : GuardCalibration.validWindow n (v.get 0) ≠ 0 := by
      intro hzero
      exact hz ((hw (ofFn ![v.get 0])).trans hzero)
    exact typedBranchCalibration n arity data hc v (validWindowOneOfNonzero n (v.get 0) hn)

theorem actualOriginalOuterScalarTypedCalibration :
    OuterNativeCalibrationTargets.ActualOriginalOuterScalarTypedCalibration := by
  intro n arity base window oldScalar oldTyped hc hw hs ht
  have hd := actualOriginalOuterSelectedDataCalibration n arity base window hc hw
  exact ⟨scalarCalibration n arity (OuterSelection.data base window) window oldScalar hd hw hs,
    typedCalibration n arity (OuterSelection.data base window) window oldTyped hd hw ht⟩

/-- Keep BOTH literal validity/Gamma and tag layers; application is copied. -/
theorem actualOriginalOuterBaseComputabilityCalibration :
    OuterNativeCalibrationTargets.ActualOriginalOuterBaseComputabilityCalibration := by
  intro n arity base window old hc hw hold
  have hd := actualOriginalOuterSelectedDataCalibration n arity base window hc hw
  have hg : ∀ v : List.Vector Nat 1, evaluate Outer.gamma v = GammaGuardCalibration.gammaValue v :=
    InternalOriginalObjectFiberSourceDispatchEvaluationProof.actualOriginalObjectSourceAuxiliaryCalibration.1
  have hv : ∀ v : List.Vector Nat 1, evaluate Outer.valid v = GammaGuardCalibration.objectValid (v.get 0) :=
    InternalOriginalObjectFiberSourceDispatchEvaluationProof.actualOriginalObjectSourceAuxiliaryCalibration.2.1
  have ht : ∀ v : List.Vector Nat 2, evaluate Outer.tag v = GuardCalibration.typeTagValue v :=
    InternalOriginalObjectFiberSourceDispatchEvaluationProof.actualOriginalObjectSourceAuxiliaryCalibration.2.2.1
  refine ⟨?_,?_,?_⟩
  · intro v
    change evaluate (GuardedSource.guardedTyped
      (GammaGuardedSource.baseTyped (Outer.typed (OuterSelection.data base window) window old.typed)
        Outer.valid) Outer.tag) v = _
    exact GuardedSourceCalibrationProof.typedCalibration n arity
      (GammaGuardedSource.baseTyped (Outer.typed (OuterSelection.data base window) window old.typed)
        Outer.valid) Outer.tag
      (GammaGuardedSourceCalibrationProof.baseTypedCalibration n arity
        (Outer.typed (OuterSelection.data base window) window old.typed) Outer.valid
        (typedCalibration n arity (OuterSelection.data base window) window old.typed hd hw hold.1) hv)
      ht v
  · intro v
    change evaluate (GammaGuardedSource.guard Outer.valid Outer.gamma) v = _
    exact GammaGuardedSourceCalibrationProof.guardCalibration Outer.valid Outer.gamma hv hg v
  · exact hold.2.2

theorem actualOriginalOuterScalarTypedFallback :
    OuterNativeCalibrationTargets.ActualOriginalOuterScalarTypedFallback := by
  intro data rawScalar window oldScalar oldTyped
  constructor
  · intro v hz
    rw [Outer.scalar,evalBranch,windowAtEvaluation,hz,if_pos rfl]
  · intro v hz
    rw [Outer.typed,evalBranch,windowAtEvaluation,hz,if_pos rfl]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterNativeCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterNativeCalibrationProof
