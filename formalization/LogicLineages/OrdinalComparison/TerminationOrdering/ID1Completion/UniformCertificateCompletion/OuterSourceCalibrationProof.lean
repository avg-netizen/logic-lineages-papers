module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSourceCalibrationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterResultCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePositiveCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSpineMeasureEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSourceCalibrationProof
open Source SourceComputabilityCompletion
open NumberedRewriteSyntax NumberedRewriteReduction
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- Concrete original shape metadata, with the complete flag and depth. -/
theorem actualOriginalConcreteShapeCalibration :
    OuterSourceCalibrationTargets.ActualOriginalConcreteShapeCalibration := by
  intro n arity Gamma tau q
  have hm := BottomSpineMeasureEvaluationProof.actualOriginalBottomSpineMeasureCalibration
    n arity Gamma tau q
  refine ⟨?_,?_,?_⟩
  · rw [BottomRepresentativeEvaluationProof.bottomTestEvaluation,
      BottomRepresentativeEvaluationProof.bottomValuePacked]
    cases NumberedBottomAccessibilitySupportProof.bottomView
      (⟨tau,q⟩ : Packed (Fin n) arity Gamma) <;> simp
  · rw [hm.1,BottomSpineMeasure.meaning,Nat.unpair_pair]
    exact hm.2
  · rw [hm.1,BottomSpineMeasure.meaning,Nat.unpair_pair]

theorem gammaAtEvaluation (value : Nat) :
    evaluate Outer.gamma (ofFn ![value]) = (Nat.unpair value).1 := by
  change evaluate InternalUnpair.left (value ::ᵥ List.Vector.nil) = _
  exact (InternalUnpairEvaluationProof.exactUnpairEvaluation value).1

/-- Only the original Object coordinates are substituted into the raw
checker; the original certificate and runtime parameter stay separate. -/
theorem positiveCompositionEvaluation (raw : Program 4) (v : List.Vector Nat 4) :
    evaluate (.composition raw
      (Fin.cons (rightOf (.projection 1)) (Fin.cons (rightOf (.projection 2))
        (Fin.cons (.projection 3) (Fin.cons (Outer.parameter (.projection 0) (.projection 1)) Fin.elim0))))) v =
      evaluate raw (ofFn ![(Nat.unpair (v.get 1)).2,(Nat.unpair (v.get 2)).2,
        v.get 3,Nat.pair (v.get 0) (Nat.unpair (v.get 1)).1]) := by
  change evaluate raw (ofFn fun i : Fin 4 => evaluate
    ((Fin.cons (rightOf (.projection 1)) (Fin.cons (rightOf (.projection 2))
      (Fin.cons (.projection 3) (Fin.cons (Outer.parameter (.projection 0) (.projection 1)) Fin.elim0))) :
        Fin 4 → Program 4) i) v) = _
  congr 1
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)))) i
  · exact rightOfEvaluation (.projection 1) v
  · exact rightOfEvaluation (.projection 2) v
  · rfl
  · exact OuterNativeCalibrationProof.parameterEvaluation (.projection 0) (.projection 1) v

theorem positiveBranchEvaluation (raw : Program 4) (v : List.Vector Nat 4) :
    evaluate (Outer.positiveBranch raw) v =
      if (Nat.unpair (v.get 1)).1 = (Nat.unpair (v.get 2)).1 ∧
        evaluate raw (ofFn ![(Nat.unpair (v.get 1)).2,(Nat.unpair (v.get 2)).2,
          v.get 3,Nat.pair (v.get 0) (Nat.unpair (v.get 1)).1]) = 1 then 1 else 0 := by
  rw [Outer.positiveBranch,actualConjunctionEvaluation,
    GammaGuardedSourceCalibrationProof.evalSameGamma,gammaAtEvaluation,gammaAtEvaluation,
    positiveCompositionEvaluation]
  by_cases h : (Nat.unpair (v.get 1)).1 = (Nat.unpair (v.get 2)).1 <;> simp [h]

/-- The raw Context is decoded but never re-encoded. The runtime positive
supplier pays both validators and shape guards before Object wrapping. -/
theorem positiveBranchCalibration (n : Nat) (arity : Fin n → Nat) (data : Data)
    (oldStep : Program 4)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (hl : InternalOriginalUniformApplicationStepSelection.LeafCalibrated n arity oldStep)
    (v : List.Vector Nat 4) (hw : GuardCalibration.validWindow n (v.get 0) = 1) :
    evaluate (Outer.positiveBranch (Outer.rawPositive data oldStep
      BottomRepresentative.bottomTest BottomSpineMeasure.measure)) v =
      ContextUniform.positiveValue n arity v := by
  obtain ⟨ctx,hctx,hS⟩ := (GuardCalibrationProof.actualValidWindowCalibration n (v.get 0)).1.mp hw
  have hp : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair (Nat.pair (v.get 0) (Nat.unpair (v.get 1)).1)).1 = some ctx := by
    simpa only [Nat.unpair_pair] using hctx
  obtain ⟨Gamma,hs⟩ := RuntimePositiveCalibrationProof.actualOriginalRuntimePositiveCalibration
    n arity data oldStep BottomRepresentative.bottomTest BottomSpineMeasure.measure hc hl
    (actualOriginalConcreteShapeCalibration n arity)
    (Nat.pair (v.get 0) (Nat.unpair (v.get 1)).1) ctx hp hS
  have ho := OuterNativeCalibrationProof.objectDecodeAt (v.get 0) (v.get 1) Gamma hs.objectSlice
  have hsource := (OuterResultCalibrationProof.objectCoordinates (v.get 1) Gamma
    (Nat.unpair (v.get 1)).2 ho).1
  obtain ⟨target,ht⟩ := JointGammaDomainCodecProof.actualObjectCodec.1 (v.get 2)
  have htarget := OuterResultCalibrationProof.objectCoordinates (v.get 2) target.1 target.2 ht
  rw [positiveBranchEvaluation,hs.positive]
  simp only [ContextUniform.positiveValue,ho,ht,OrdinaryArithmeticQuotient.positiveValue,
    List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,hctx,Option.any_some,hsource,htarget.1,htarget.2]
  by_cases hg : Gamma = target.1
  · have he : Encodable.encode Gamma = Encodable.encode target.1 := congrArg Encodable.encode hg
    rw [if_pos hg]
    cases hb : NumberedQuotientPathCertificates.positivePathTest
      n arity ctx.1.1 ctx.1.2 Gamma ctx.2 (Nat.unpair (v.get 1)).2 target.2 (v.get 3) <;>
      simp [he,hb]
  · have he : Encodable.encode Gamma ≠ Encodable.encode target.1 := fun he => hg (Encodable.encode_injective he)
    simp [hg,he]

theorem actualOriginalOuterPositiveCalibration :
    OuterSourceCalibrationTargets.ActualOriginalOuterPositiveCalibration := by
  intro n arity base window oldStep oldPositive hc hw hl hold v
  have hd := OuterNativeCalibrationProof.actualOriginalOuterSelectedDataCalibration
    n arity base window hc hw
  rw [OuterSourceCalibration.positive,Outer.positive,evalBranch,
    OuterNativeCalibrationProof.windowAtEvaluation]
  by_cases hz : evaluate window (ofFn ![v.get 0]) = 0
  · rw [if_pos hz]
    exact hold v
  · rw [if_neg hz]
    have hn : GuardCalibration.validWindow n (v.get 0) ≠ 0 := by
      intro hzero
      exact hz ((hw (ofFn ![v.get 0])).trans hzero)
    exact positiveBranchCalibration n arity (OuterSelection.data base window) oldStep hd hl v
      (OuterNativeCalibrationProof.validWindowOneOfNonzero n (v.get 0) hn)

/-- Reuse the original Gamma and typed/tag source constructors, retaining
the four exact old field calibrations and the same typed branch. -/
theorem actualOriginalOuterSourceCalibration :
    OuterSourceCalibrationTargets.ActualOriginalOuterSourceCalibration := by
  intro n arity base window oldSrc oldComp oldStep hc hw hs hcomp hl
  let data := OuterSelection.data base window
  let rawScalar := RawScalar.checker data
  let rawPositive := Outer.rawPositive data oldStep
    BottomRepresentative.bottomTest BottomSpineMeasure.measure
  let sourceBase := Outer.sourceBase oldSrc rawScalar rawPositive window
  let compBase : JointGammaComputability.Data :=
    { oldComp with typed := Outer.typed data window oldComp.typed }
  have hst := OuterNativeCalibrationProof.actualOriginalOuterScalarTypedCalibration
    n arity base window oldSrc.scalar oldComp.typed hc hw hs.1 hcomp.1
  have hp := actualOriginalOuterPositiveCalibration n arity base window oldStep oldSrc.positive
    hc hw hl hs.2.2.1
  have hsourceBase : ContextUniform.Calibrated sourceBase n arity :=
    ⟨hst.scalar,hs.2.1,hp,hs.2.2.2⟩
  have hcompBase : JointGammaComputability.Calibrated compBase n arity := ⟨hst.typed,hcomp.2⟩
  have hg : ∀ v : List.Vector Nat 1, evaluate Outer.gamma v = GammaGuardCalibration.gammaValue v :=
    InternalOriginalObjectFiberSourceDispatchEvaluationProof.actualOriginalObjectSourceAuxiliaryCalibration.1
  have hv : ∀ v : List.Vector Nat 1,
      evaluate Outer.valid v = GammaGuardCalibration.objectValid (v.get 0) :=
    InternalOriginalObjectFiberSourceDispatchEvaluationProof.actualOriginalObjectSourceAuxiliaryCalibration.2.1
  have ht : ∀ v : List.Vector Nat 2, evaluate Outer.tag v = GuardCalibration.typeTagValue v :=
    InternalOriginalObjectFiberSourceDispatchEvaluationProof.actualOriginalObjectSourceAuxiliaryCalibration.2.2.1
  obtain ⟨hbs,hbc⟩ := GammaGuardedSourceCalibrationProof.actualBaseCalibration
    n arity sourceBase compBase Outer.valid Outer.gamma hsourceBase hcompBase hv hg
  exact (GuardedSourceCalibrationProof.actualGuardedCalibration n arity
    (GammaGuardedSource.baseSource sourceBase Outer.gamma)
    (GammaGuardedSource.baseComputability compBase Outer.valid Outer.gamma)
    Outer.tag window hbs hbc ht hw).1

theorem liftEvaluation (data : Data) (window : Program 1) (oldVertex : Program 5)
    (v : List.Vector Nat 5) :
    evaluate (Outer.lift data window oldVertex) v =
      evaluate (InternalApplicationPathMap.pathMap (Path.vertex data window oldVertex))
        (ofFn ![v.get 4,Nat.pair (v.get 0) (Nat.unpair (v.get 3)).1,
          v.get 1,v.get 2,(Nat.unpair (v.get 3)).2]) := by
  change evaluate (InternalApplicationPathMap.pathMap (Path.vertex data window oldVertex))
    (ofFn fun i : Fin 5 => evaluate
      ((Fin.cons (.projection 4) (Fin.cons (Outer.parameter (.projection 0) (.projection 3))
        (Fin.cons (.projection 1) (Fin.cons (.projection 2)
          (Fin.cons (rightOf (.projection 3)) Fin.elim0)))) : Fin 5 → Program 5) i) v) = _
  congr 1
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (fun j => Fin.elim0 j))))) i
  · rfl
  · exact OuterNativeCalibrationProof.parameterEvaluation (.projection 0) (.projection 3) v
  · rfl
  · rfl
  · exact rightOfEvaluation (.projection 3) v

/-- One actual Gamma at the original argument parameter covers every
certificate, including every raw Context and original off-domain default. -/
theorem actualOriginalOuterObjectLiftCalibration :
    OuterSourceCalibrationTargets.ActualOriginalOuterObjectLiftCalibration := by
  intro n arity base window oldVertex hc hw hold v
  have hd := OuterNativeCalibrationProof.actualOriginalOuterSelectedDataCalibration
    n arity base window hc hw
  have hr := RuntimePathCalibrationProof.actualOriginalRuntimePathCalibration
    n arity (OuterSelection.data base window) window oldVertex hd hw hold
  obtain ⟨Gamma,ho,_,hmap⟩ := hr.slices (Nat.pair (v.get 0) (Nat.unpair (v.get 3)).1)
  have ha := OuterNativeCalibrationProof.objectDecodeAt (v.get 0) (v.get 3) Gamma ho
  rw [OuterSelection.lift,liftEvaluation]
  have hm := hmap (v.get 1) (v.get 2) (Nat.unpair (v.get 3)).2 (v.get 4)
  simpa only [Nat.unpair_pair,ApplicationCertificateLiftPath.pathValue,ha,
    Option.map_some,Option.getD_some] using hm

theorem actualOriginalOuterPositiveSourceFallback :
    OuterSourceCalibrationTargets.ActualOriginalOuterPositiveSourceFallback := by
  intro data rawScalar oldStep bottom measure window oldPositive oldSrc oldComp
  refine ⟨?_,rfl,rfl⟩
  intro v hz
  rw [Outer.positive,evalBranch,OuterNativeCalibrationProof.windowAtEvaluation,hz,if_pos rfl]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSourceCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSourceCalibrationProof
