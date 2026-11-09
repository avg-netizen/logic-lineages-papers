module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformObjectPathDispatchTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathMapEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformObjectPathDispatchEvaluationProof
open Source InternalOriginalUniformObjectPathDispatch InternalOriginalUniformObjectPathDispatchTargets
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open InternalOriginalUniformParameterLeaves (parameterCode)
open InternalCanonicalFixedWindowVertexDispatchEvaluationProof (constantEvaluation)
open InternalOriginalObjectFiberPathDispatchEvaluationProof (objectCodePair)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem windowTestEvaluation (window : Nat) (xs : List.Vector Nat 5) :
    evaluate (windowTest window) xs = if xs.get 0 = window then 1 else 0 := by
  rw [windowTest,sameEvaluation,constantEvaluation]
  rfl

theorem runtimeParameterEvaluation (xs : List.Vector Nat 5) :
    evaluate runtimeParameter xs = Nat.pair (xs.get 0) (Nat.unpair (xs.get 3)).1 := by
  rw [runtimeParameter,pairOfEvaluation,leftOfEvaluation]
  rfl

theorem activeBranchEvaluation (vertexProgram : Program 5) (xs : List.Vector Nat 5) :
    evaluate (activeBranch vertexProgram) xs =
      evaluate (InternalApplicationPathMap.pathMap vertexProgram)
        (List.Vector.ofFn ![xs.get 4,Nat.pair (xs.get 0) (Nat.unpair (xs.get 3)).1,
          xs.get 1,xs.get 2,(Nat.unpair (xs.get 3)).2]) := by
  change evaluate (InternalApplicationPathMap.pathMap vertexProgram)
    (List.Vector.ofFn fun i : Fin 5 => evaluate
      ((![Program.projection 4,runtimeParameter,.projection 1,.projection 2,
        rightOf (.projection 3)] : Fin 5 → Program 5) i) xs) = _
  congr 1
  apply List.Vector.ext
  intro i
  exact Fin.cases rfl (Fin.cases (runtimeParameterEvaluation xs)
    (Fin.cases rfl (Fin.cases rfl
      (Fin.cases (rightOfEvaluation (.projection 3) xs) (fun q => Fin.elim0 q))))) i

theorem dispatchEvaluation (window : Nat) (vertexProgram oldLift : Program 5)
    (xs : List.Vector Nat 5) :
    evaluate (dispatch window vertexProgram oldLift) xs =
      if xs.get 0 = window then
        evaluate (InternalApplicationPathMap.pathMap vertexProgram)
          (List.Vector.ofFn ![xs.get 4,Nat.pair (xs.get 0) (Nat.unpair (xs.get 3)).1,
            xs.get 1,xs.get 2,(Nat.unpair (xs.get 3)).2])
      else evaluate oldLift xs := by
  rw [dispatch,evalBranch,windowTestEvaluation]
  by_cases h : xs.get 0 = window
  · simp only [h,if_true,Nat.one_ne_zero,if_false]
    simpa only [h] using activeBranchEvaluation vertexProgram xs
  · simp only [h,if_false,if_true]

/-- The actual original Object decoder is total. Its decoded Gamma enters
only this external calibration proof; the internal graph law has a symbolic
GammaCode and uses only original pairing/unpair derivations. -/
theorem actualOriginalUniformObjectPathCalibration :
    ActualOriginalUniformObjectPathCalibration := by
  intro n arity data oldVertex oldLift hdata hvertex hlift symbols S table hS xs
  rw [dispatchEvaluation]
  by_cases hwindow : xs.get 0 = OrdinaryArithmeticQuotient.contextCode symbols S table
  · rw [if_pos hwindow]
    obtain ⟨⟨Gamma,argument⟩,hdecode⟩ := JointGammaDomainCodecProof.actualObjectCodec.1 (xs.get 3)
    have hencode := (JointGammaDomainCodecProof.actualObjectCodec.2.1
      (xs.get 3) (Gamma,argument)).mp hdecode
    change ContextUniform.objectCode Gamma argument = xs.get 3 at hencode
    rw [objectCodePair] at hencode
    have hleft : (Nat.unpair (xs.get 3)).1 = Encodable.encode Gamma := by
      rw [← hencode,Nat.unpair_pair]
    have hright : (Nat.unpair (xs.get 3)).2 = argument := by
      rw [← hencode,Nat.unpair_pair]
    have hmap := (InternalOriginalUniformVertexPathMapEvaluationProof.actualOriginalUniformVertexPathCalibration
      n arity data oldVertex hdata hvertex symbols S Gamma table hS).2
      (xs.get 1) (xs.get 2) argument (xs.get 4)
    calc
      _ = ApplicationCertificateLiftPath.liftPath n arity Gamma
          (OrdinaryArithmeticQuotient.contextCode symbols S table)
          (xs.get 1) (xs.get 2) argument (xs.get 4) := by
        simpa only [hwindow,hleft,hright,parameterCode] using hmap
      _ = ApplicationCertificateLiftPath.pathValue n arity xs := by
        unfold ApplicationCertificateLiftPath.pathValue
        rw [hdecode]
        simp only [Option.map_some,Option.getD_some]
        rw [hwindow]
  · rw [if_neg hwindow]
    exact hlift xs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformObjectPathDispatchEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformObjectPathDispatchEvaluationProof
