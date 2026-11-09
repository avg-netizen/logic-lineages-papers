module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterResultCalibrationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterNativeCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePathCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterResultCalibrationProof
open Source
open InternalOriginalUniformDescentSelection (Data)
open InternalOriginalUniformParameterLeaves (parameterObject)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalOriginalObjectFiberSourceDispatchEvaluationProof (objectCodePair)
open InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- Use the original arrow AST, not a newly selected arrow program. -/
theorem arrowCalibration (v : List.Vector Nat 2) :
    evaluate Outer.arrow v = ApplicationDomain.arrowValue v :=
  InternalOriginalObjectFiberSourceDispatchEvaluationProof.actualOriginalObjectSourceAuxiliaryCalibration.2.2.2 v

theorem actualOriginalOuterResultActivationCalibration :
    OuterResultCalibrationTargets.ActualOriginalOuterResultActivationCalibration := by
  intro n arity base window old hc hw hold
  have hb := OuterNativeCalibrationProof.actualOriginalOuterBaseComputabilityCalibration
    n arity base window old hc hw hold
  exact ApplicationDomainProgramProof.actualExplicitActivation n arity window
    (Outer.baseComputability old (OuterSelection.data base window) window).typed
    (Outer.baseComputability old (OuterSelection.data base window) window).guard
    Outer.arrow hw hb.1 hb.2.1 arrowCalibration

theorem vectorFive (v : List.Vector Nat 5) :
    ofFn ![v.get 0,v.get 1,v.get 2,v.get 3,v.get 4] = v := by
  apply List.Vector.ext
  intro i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (fun q => Fin.elim0 q))))) i

/-- Evaluate the literal paired branch at its unchanged five raw inputs. -/
theorem resultBranchEvaluation (vertex : Program 5) (v : List.Vector Nat 5) :
    evaluate (Outer.resultBranch vertex) v =
      Nat.pair (Nat.unpair (v.get 3)).1 (evaluate vertex
        (ofFn ![Nat.pair (v.get 0) (Nat.unpair (v.get 3)).1,v.get 1,v.get 2,
          (Nat.unpair (v.get 4)).2,(Nat.unpair (v.get 3)).2])) := by
  rw [Outer.resultBranch,pairOfEvaluation,leftOfEvaluation]
  congr 1
  change evaluate vertex (ofFn fun i : Fin 5 => evaluate
    ((Fin.cons (Outer.parameter (.projection 0) (.projection 3))
      (Fin.cons (.projection 1) (Fin.cons (.projection 2)
        (Fin.cons (rightOf (.projection 4)) (Fin.cons (rightOf (.projection 3)) Fin.elim0)))) :
          Fin 5 → Program 5) i) v) = _
  congr 1
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (fun q => Fin.elim0 q))))) i
  · exact OuterNativeCalibrationProof.parameterEvaluation (.projection 0) (.projection 3) v
  · rfl
  · rfl
  · exact rightOfEvaluation (.projection 4) v
  · exact rightOfEvaluation (.projection 3) v

/-- Invert only the original total Object codec, never a raw Context code. -/
theorem objectCoordinates (object : Nat) (Gamma : List Ty) (payload : Nat)
    (hd : Encodable.decode (α := ContextUniform.Object) object = some (Gamma,payload)) :
    (Nat.unpair object).1 = Encodable.encode Gamma ∧ (Nat.unpair object).2 = payload := by
  have he := (JointGammaDomainCodecProof.actualObjectCodec.2.1 object (Gamma,payload)).mp hd
  rw [objectCodePair] at he
  rw [← he,Nat.unpair_pair]
  exact ⟨rfl,rfl⟩

theorem parameterSliceFromObject (context object : Nat) (Gamma : List Ty) (payload : Nat)
    (hd : Encodable.decode (α := ContextUniform.Object) object = some (Gamma,payload)) :
    ∀ value : Nat,
      parameterObject value (Nat.pair context (Nat.unpair object).1) = some (Gamma,value) := by
  have hl := (objectCoordinates object Gamma payload hd).1
  intro value
  simp only [parameterObject,Nat.unpair_pair,hl]
  exact (JointGammaDomainCodecProof.actualObjectCodec.2.1 _ (Gamma,value)).mpr
    (objectCodePair Gamma value)

/-- Use the accepted raw-parameter vertex calibration without unfolding its
program AST into the semantic proof. Original function and argument Objects
supply the coordinates and one common Gamma. -/
theorem rawVertexAtObjects (n : Nat) (arity : Fin n → Nat) (data : Data)
    (window : Program 1) (oldVertex : Program 5)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (hw : Path.windowCalibrated n window)
    (hold : ∀ v : List.Vector Nat 5, evaluate oldVertex v = RuntimeVertex.value n arity v)
    (v : List.Vector Nat 5) (Gamma : List Ty) (x y : Nat)
    (hf : Encodable.decode (α := ContextUniform.Object) (v.get 3) = some (Gamma,x))
    (ha : Encodable.decode (α := ContextUniform.Object) (v.get 4) = some (Gamma,y)) :
    evaluate (Path.vertex data window oldVertex)
      (ofFn ![Nat.pair (v.get 0) (Nat.unpair (v.get 3)).1,v.get 1,v.get 2,
        (Nat.unpair (v.get 4)).2,(Nat.unpair (v.get 3)).2]) =
      ApplicationCertificateLiftPath.vertex n arity Gamma (v.get 0) (v.get 1) (v.get 2) y x := by
  have hfr := (objectCoordinates (v.get 3) Gamma x hf).2
  have har := (objectCoordinates (v.get 4) Gamma y ha).2
  have hp := parameterSliceFromObject (v.get 0) (v.get 3) Gamma x hf
  rw [RuntimePathCalibrationProof.vertexCalibration n arity data window oldVertex hc hw hold]
  simpa only [List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,
    Nat.unpair_pair,hfr,har] using
    RuntimePathCalibrationProof.runtimeValueAt n arity
      (ofFn ![Nat.pair (v.get 0) (Nat.unpair (v.get 3)).1,v.get 1,v.get 2,
        (Nat.unpair (v.get 4)).2,(Nat.unpair (v.get 3)).2]) Gamma hp

/-- This equation alone does not claim success: the inner vertex still has
its original getD 0 default. Full Option success is proved separately below. -/
theorem resultBranchAtObjects (n : Nat) (arity : Fin n → Nat) (data : Data)
    (window : Program 1) (oldVertex : Program 5)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (hw : Path.windowCalibrated n window)
    (hold : ∀ v : List.Vector Nat 5, evaluate oldVertex v = RuntimeVertex.value n arity v)
    (v : List.Vector Nat 5) (Gamma : List Ty) (x y : Nat)
    (hf : Encodable.decode (α := ContextUniform.Object) (v.get 3) = some (Gamma,x))
    (ha : Encodable.decode (α := ContextUniform.Object) (v.get 4) = some (Gamma,y)) :
    evaluate (Outer.resultBranch (Path.vertex data window oldVertex)) v =
      ContextUniform.objectCode Gamma
        (ApplicationCertificateLiftPath.vertex n arity Gamma (v.get 0) (v.get 1) (v.get 2) y x) := by
  rw [resultBranchEvaluation,rawVertexAtObjects n arity data window oldVertex hc hw hold v Gamma x y hf ha,
    (objectCoordinates (v.get 3) Gamma x hf).1,objectCodePair]

theorem resultOptionAtObjects (n : Nat) (arity : Fin n → Nat)
    (v : List.Vector Nat 5) (Gamma : List Ty) (x y : Nat)
    (hf : Encodable.decode (α := ContextUniform.Object) (v.get 3) = some (Gamma,x))
    (ha : Encodable.decode (α := ContextUniform.Object) (v.get 4) = some (Gamma,y)) :
    ApplicationResultBuilder.resultOption n arity v =
      (OrdinaryArithmeticApplication.decodedApplication n arity Gamma
        (v.get 0) (v.get 1) (v.get 2) x y).map (ContextUniform.objectCode Gamma) := by
  simp [ApplicationResultBuilder.resultOption,hf,ha]

/-- The original domain theorem establishes full success independently of
the raw vertex and its default. The input vector is not reconstructed as a
new context or Object encoding. -/
theorem domainSuccessAt (n : Nat) (arity : Fin n → Nat)
    (v : List.Vector Nat 5) (ha : ApplicationDomain.active n arity v) :
    ApplicationResultBuilder.resultOption n arity v =
      some (ApplicationResultBuilder.resultValue n arity v) := by
  have hs := (ApplicationDomainProof.actualDomainSuccess n arity
    (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4)
    (by simpa only [vectorFive] using ha)).1
  simpa only [vectorFive] using hs

/-- Full original Option success, including code zero, identifies the
actual paired branch. No H=1 or nonzero-output inference is used. -/
theorem resultBranchSuccess (n : Nat) (arity : Fin n → Nat) (data : Data)
    (window : Program 1) (oldVertex : Program 5)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (hw : Path.windowCalibrated n window)
    (hold : ∀ v : List.Vector Nat 5, evaluate oldVertex v = RuntimeVertex.value n arity v)
    (v : List.Vector Nat 5) (ha : ApplicationDomain.active n arity v) :
    ApplicationResultBuilder.resultOption n arity v =
      some (evaluate (Outer.resultBranch (Path.vertex data window oldVertex)) v) := by
  have hs := domainSuccessAt n arity v ha
  obtain ⟨Gamma,x,y,hf,hy⟩ :=
    (JointGammaDomainProof.actualGuardCalibration.1 (v.get 3) (v.get 4)).mp ha.2.2.2
  have ho := resultOptionAtObjects n arity v Gamma x y hf hy
  rw [ho] at hs
  rw [ho,resultBranchAtObjects n arity data window oldVertex hc hw hold v Gamma x y hf hy]
  cases hd : OrdinaryArithmeticApplication.decodedApplication n arity Gamma
      (v.get 0) (v.get 1) (v.get 2) x y with
  | none =>
    rw [hd,Option.map_none] at hs
    cases hs
  | some raw =>
    simp only [Option.map_some,ApplicationCertificateLiftPath.vertex,hd,Option.getD_some]

/-- The active branch needs no calibration of its unused oldResult. -/
theorem actualOriginalOuterActiveResultSuccess :
    OuterResultCalibrationTargets.ActualOriginalOuterActiveResultSuccess := by
  intro n arity base window old oldVertex oldResult hc hw hold hv v ha
  have hd := OuterNativeCalibrationProof.actualOriginalOuterSelectedDataCalibration
    n arity base window hc hw
  have hactivation := actualOriginalOuterResultActivationCalibration n arity base window old hc hw hold v
  have hactive := (ApplicationDomainProgramProof.actualActivationCalibration n arity v).2.1.mp
    (hactivation.symm.trans ha)
  have hs := resultBranchSuccess n arity (OuterSelection.data base window) window oldVertex hd hw hv v hactive
  have he : evaluate (Outer.result old (OuterSelection.data base window) window oldVertex oldResult) v =
      evaluate (Outer.resultBranch (Path.vertex (OuterSelection.data base window) window oldVertex)) v := by
    rw [Outer.result,evalBranch,ha]
    rfl
  have hsuc := ((ApplicationResultBuilderProof.partialTotal n arity v _).mp hs).1
  refine ⟨hs,?_,hsuc,?_⟩
  · simpa only [he] using hs
  · intro hz
    rw [he] at hz
    simpa only [hz] using hs

theorem resultCalibration (n : Nat) (arity : Fin n → Nat) (base : Data)
    (window : Program 1) (old : JointGammaComputability.Data) (oldVertex oldResult : Program 5)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity base)
    (hw : Path.windowCalibrated n window) (hold : JointGammaComputability.Calibrated old n arity)
    (hv : ∀ v : List.Vector Nat 5, evaluate oldVertex v = RuntimeVertex.value n arity v)
    (hr : ∀ v : List.Vector Nat 5, evaluate oldResult v = ApplicationResultBuilder.resultValue n arity v)
    (v : List.Vector Nat 5) :
    evaluate (Outer.result old (OuterSelection.data base window) window oldVertex oldResult) v =
      ApplicationResultBuilder.resultValue n arity v := by
  by_cases hz : evaluate (Outer.resultActivation old (OuterSelection.data base window) window) v = 0
  · rw [Outer.result,evalBranch,hz,if_pos rfl]
    exact hr v
  · have hactivation := actualOriginalOuterResultActivationCalibration n arity base window old hc hw hold v
    have hone : evaluate (Outer.resultActivation old (OuterSelection.data base window) window) v = 1 := by
      rcases (ApplicationDomainProgramProof.actualActivationCalibration n arity v).1 with hzero | hone
      · exact False.elim (hz (hactivation.trans hzero))
      · exact hactivation.trans hone
    have hs := (actualOriginalOuterActiveResultSuccess n arity base window old oldVertex oldResult
      hc hw hold hv v hone).2.1
    exact ((ApplicationResultBuilderProof.partialTotal n arity v _).mp hs).2

theorem actualOriginalOuterResultComputabilityCalibration :
    OuterResultCalibrationTargets.ActualOriginalOuterResultComputabilityCalibration := by
  intro n arity base window old oldVertex oldResult hc hw hold hv hr
  have hb := OuterNativeCalibrationProof.actualOriginalOuterBaseComputabilityCalibration
    n arity base window old hc hw hold
  have hresult := resultCalibration n arity base window old oldVertex oldResult hc hw hold hv hr
  refine ⟨hresult,?_⟩
  exact InternalApplicationCalibrationProof.actualCalibration n arity
    (Outer.baseComputability old (OuterSelection.data base window) window) window Outer.arrow
    (Outer.result old (OuterSelection.data base window) window oldVertex oldResult)
    hb hw arrowCalibration hresult

theorem actualOriginalOuterResultApplicationFallback :
    OuterResultCalibrationTargets.ActualOriginalOuterResultApplicationFallback := by
  intro data window old oldVertex oldResult
  constructor
  · intro v hz
    rw [Outer.result,evalBranch,hz,if_pos rfl]
  · intro v hz
    change evaluate (InternalApplication.application (Outer.resultActivation old data window)
      (Outer.result old data window oldVertex oldResult) old.application) v = _
    rw [InternalApplication.application,evalBranch,InternalApplicationCalibrationProof.evaluateFirstFive,
      hz,if_pos rfl]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterResultCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterResultCalibrationProof
