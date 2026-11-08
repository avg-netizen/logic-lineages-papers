module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainCodecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowPathLiftEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchEvaluationProof
open Source InternalOriginalObjectFiberPathDispatch
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof
open InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original product encoder, with its raw natural second coordinate. -/
theorem objectCodePair (Gamma : List Ty) (argument : Nat) :
    ContextUniform.objectCode Gamma argument = Nat.pair (Encodable.encode Gamma) argument := by
  exact Encodable.encode_prod_val Gamma argument

/-- Totality and the fixed fiber are properties of the unchanged original
codec. No decoder is installed and no internal graph is redefined. -/
theorem actualOriginalObjectFiberCodec :
    InternalOriginalObjectFiberPathDispatchTargets.ActualOriginalObjectFiberCodec := by
  refine ⟨JointGammaDomainCodecProof.actualObjectCodec.1,objectCodePair,?_⟩
  intro Gamma argumentObject
  rw [JointGammaDomainCodecProof.actualObjectCodec.2.1
    argumentObject (Gamma,(Nat.unpair argumentObject).2),objectCodePair]
  constructor
  · intro h
    have hu := congrArg (fun code => (Nat.unpair code).1) h
    simpa only [Nat.unpair_pair] using hu.symm
  · intro h
    rw [← h]
    exact Nat.pair_unpair argumentObject

/-- The actual equality-test AST observes the actual unpair-left AST. -/
theorem fiberTestEvaluation (Gamma : List Ty) (xs : List.Vector Nat 5) :
    evaluate (fiberTest Gamma) xs =
      if (Nat.unpair (xs.get 3)).1 = Encodable.encode Gamma then 1 else 0 := by
  rw [fiberTest,sameEvaluation,leftOfEvaluation,
    InternalCanonicalFixedWindowVertexDispatchEvaluationProof.constantEvaluation]
  rfl

/-- The active composition uses the original pathMap, with certificate first
and the unmodified right coordinate of the original object last. -/
theorem activeBranchEvaluation (vertexProgram : Program 5) (xs : List.Vector Nat 5) :
    evaluate (activeBranch vertexProgram) xs =
      evaluate (InternalApplicationPathMap.pathMap vertexProgram)
        (List.Vector.ofFn ![xs.get 4,xs.get 0,xs.get 1,xs.get 2,
          (Nat.unpair (xs.get 3)).2]) := by
  change evaluate (InternalApplicationPathMap.pathMap vertexProgram)
    (List.Vector.ofFn fun i : Fin 5 =>
      evaluate ((![Program.projection 4,.projection 0,.projection 1,.projection 2,
        rightOf (.projection 3)] : Fin 5 → Program 5) i) xs) = _
  congr 1
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (fun j => Fin.elim0 j))))) i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact rightOfEvaluation (.projection 3) xs

/-- Exact branch semantics, including all inactive inputs unchanged. -/
theorem actualOriginalObjectFiberDispatchEvaluation :
    InternalOriginalObjectFiberPathDispatchTargets.ActualOriginalObjectFiberDispatchEvaluation := by
  intro Gamma vertexProgram oldLift xs
  rw [dispatch,evalBranch,fiberTestEvaluation]
  by_cases h : (Nat.unpair (xs.get 3)).1 = Encodable.encode Gamma
  · simp only [h,if_true,Nat.one_ne_zero,if_false]
    exact activeBranchEvaluation vertexProgram xs
  · simp only [h,if_false,if_true]

/-- Calibration is inherited for arbitrary contexts, not merely well-formed
or selected-window context codes. The inactive branch uses oldLift verbatim. -/
theorem actualOriginalObjectFiberPathValueCalibration :
    InternalOriginalObjectFiberPathDispatchTargets.ActualOriginalObjectFiberPathValueCalibration := by
  intro n arity symbols S Gamma table data oldVertex oldLift hc hdata hvertex hold xs
  rw [actualOriginalObjectFiberDispatchEvaluation]
  by_cases h : (Nat.unpair (xs.get 3)).1 = Encodable.encode Gamma
  · rw [if_pos h]
    have hd := (actualOriginalObjectFiberCodec.2.2 Gamma (xs.get 3)).mpr h
    have hp :=
      InternalCanonicalFixedWindowPathLiftEvaluationProof.actualOriginalCanonicalFixedWindowDecodedPathValue
        n arity symbols S Gamma table data oldVertex hc hdata hvertex
        (xs.get 0) (xs.get 1) (xs.get 2) (xs.get 3)
        (Nat.unpair (xs.get 3)).2 (xs.get 4) hd
    have hx : List.Vector.ofFn ![xs.get 0,xs.get 1,xs.get 2,xs.get 3,xs.get 4] = xs := by
      apply List.Vector.ext
      intro i
      refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
        (Fin.cases ?_ (fun j => Fin.elim0 j))))) i <;> rfl
    rw [hx] at hp
    exact hp
  · rw [if_neg h]
    exact hold xs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchEvaluationProof
