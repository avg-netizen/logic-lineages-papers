module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumReflexiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumScanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumCalibrationProof
open Source OriginalTransparentMinimum InternalOriginalUniformParameterLeaves
open OriginalTransparentMinimumReflexiveProof OriginalTransparentMinimumScanProof
open InternalAcceptanceCalibrationProof InternalEqualityTestEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

theorem minimumEvaluation (T : Program 2) (P : Program 3) (seed parameter : Nat) :
    evaluate (minimum T P) (ofFn ![seed,parameter]) =
      if evaluate T (ofFn ![seed,parameter]) = 1 then
        (List.range (seed+1)).findIdx (fun candidate => decide
          (evaluate (reflexiveClassTest T P) (ofFn ![seed,candidate,parameter]) = 1))
      else 0 := by
  have he : evaluate (.composition InternalEqualityTest.equalityTest
      ![T,InternalLessThan.constantOne 2]) (ofFn ![seed,parameter]) =
      if evaluate T (ofFn ![seed,parameter]) = 1 then 1 else 0 := by
    change evaluate InternalEqualityTest.equalityTest
      (ofFn ![evaluate T (ofFn ![seed,parameter]),1]) = _
    rw [vectorTwo]
    exact exactEqualityEvaluation _ _
  rw [minimum,evalBranch,he]
  by_cases ht : evaluate T (ofFn ![seed,parameter]) = 1
  · simp only [ht,ite_true,Nat.one_ne_zero,ite_false]
    change evaluate (scan (reflexiveClassTest T P)) (ofFn ![seed+1,seed,parameter]) = _
    exact scanEvaluation _ _ _ _
  · simp only [ht,ite_false,ite_true]
    rfl

theorem rawPackedNumber {n : Nat} (arity : Fin n → Nat) (Gamma : List Ty)
    (seed : Nat) (q : NumberedUniformPackedDecoding.RawPacked n)
    (hq : NumberedUniformPackedDecoding.rawPackedDecode n arity Gamma seed = some q) :
    ContextUniformPrimary.packedNumber q = seed := by
  rw [NumberedUniformPackedDecodingProof.rawPackedCalibration] at hq
  obtain ⟨a,ha,he⟩ := Option.map_eq_some_iff.mp hq
  cases he
  exact NumberedNumericDecodingProof.packedNumericSound n arity Gamma seed a ha

/-- All malformed contexts and rejected packed terms retain the original zero
case; accepted terms search precisely the original packed-number bound. -/
theorem actualOriginalTransparentMinimumCalibration :
    OriginalTransparentMinimumTargets.ActualOriginalTransparentMinimumCalibration := by
  intro n arity H G P hH hG hP v
  have hPe : ∀ w, evaluate P w = classValue n arity w := hP
  have atInput (seed parameter : Nat) :
      evaluate (minimum (OriginalTypedDecoder.target H G) P) (ofFn ![seed,parameter]) =
        representativeValue n arity (ofFn ![seed,parameter]) := by
    have hitEvaluation (candidate : Nat) :
        evaluate (reflexiveClassTest (OriginalTypedDecoder.target H G) P)
          (ofFn ![seed,candidate,parameter]) =
        classValue n arity (ofFn ![seed,candidate,parameter]) :=
      (actualOriginalTransparentMinimumReflexiveCalibration n arity H G P hH hG hP _).trans
        (hPe _)
    rw [minimumEvaluation,
      OriginalTypedDecoderTargetLeafProof.actualOriginalTypedTargetLeafCalibration
        n arity H G hH hG (ofFn ![seed,parameter])]
    simp only [hitEvaluation]
    change (if decodedValue n (fun _ obj =>
        (NumberedUniformPackedDecoding.rawPackedDecode n arity obj.1 obj.2).isSome.toNat)
        seed parameter = 1 then
      (List.range (seed+1)).findIdx (fun candidate => decide
        (decodedValue n (fun ctx obj =>
          ((NumberedUniformPackedDecoding.rawPackedDecode n arity obj.1 obj.2).any
            (fun q => ContextUniformPrimary.classNumberTest arity ctx.1.1 ctx.1.2 obj.1 q candidate)).toNat)
          seed parameter = 1)) else 0) =
      decodedValue n (fun ctx obj =>
        ((NumberedUniformPackedDecoding.rawPackedDecode n arity obj.1 obj.2).map
          (ContextUniformPrimary.representative arity ctx.1.1 ctx.1.2 obj.1)).getD 0)
        seed parameter
    obtain ⟨Gamma,ho⟩ := BottomRepresentativeEvaluationProof.parameterGamma parameter
    simp only [decodedValue,ho seed]
    cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
        (Nat.unpair parameter).1 with
    | none => rfl
    | some ctx =>
      change (if (NumberedUniformPackedDecoding.rawPackedDecode n arity Gamma seed).isSome.toNat = 1
        then (List.range (seed+1)).findIdx (fun candidate => decide
          (((NumberedUniformPackedDecoding.rawPackedDecode n arity Gamma seed).any
            (fun q => ContextUniformPrimary.classNumberTest arity ctx.1.1 ctx.1.2 Gamma q candidate)).toNat = 1))
        else 0) =
        ((NumberedUniformPackedDecoding.rawPackedDecode n arity Gamma seed).map
          (ContextUniformPrimary.representative arity ctx.1.1 ctx.1.2 Gamma)).getD 0
      cases hd : NumberedUniformPackedDecoding.rawPackedDecode n arity Gamma seed with
      | none => rfl
      | some q =>
        change (List.range (seed+1)).findIdx (fun candidate => decide
            ((ContextUniformPrimary.classNumberTest arity ctx.1.1 ctx.1.2 Gamma q candidate).toNat = 1)) =
          ContextUniformPrimary.representative arity ctx.1.1 ctx.1.2 Gamma q
        rw [ContextUniformPrimary.representative,rawPackedNumber arity Gamma seed q hd]
        congr 1
        funext candidate
        cases ContextUniformPrimary.classNumberTest arity ctx.1.1 ctx.1.2 Gamma q candidate <;> rfl
  have hv : v = ofFn ![v.get 0,v.get 1] := by
    apply List.Vector.ext
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i <;> rfl
  simpa only [← hv] using atInput (v.get 0) (v.get 1)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumCalibrationProof
