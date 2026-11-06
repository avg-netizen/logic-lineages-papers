module
public import LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.Targets
import LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.MRDPFamilyProof
import LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.ProgramsProof
import LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.ScalarSemanticProof
import LogicLineages.ComputabilityKnowledge.WWBoundedVectorPaddingProof
import LogicLineages.ComputabilityKnowledge.WWOrdinalPrefixCodeProof

public section
namespace LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.VectorProof
open PositiveExpression WWOrdinalTermSemantics WWBoundedVectorPadding
open DiophantineCompletion.Specialization

private theorem encodedLists_injective (d : Nat)
    {xs ys : List (Term (Fin d))}
    (h : xs.map WWOrdinalPrefixCode.encode = ys.map WWOrdinalPrefixCode.encode) :
    xs = ys :=
  (List.map_injective_iff.mpr (WWOrdinalPrefixCodeProof.encodingInjective d)) h

private theorem vectorComparison_vectorCode {d : Nat} (weak : Bool)
    (xs ys : List (Term (Fin d))) (hbounded : BoundedSourcePair xs ys) :
    VectorComparison weak (vectorCode xs ys) ↔
      if weak then VectorLE xs ys else VectorLT xs ys := by
  constructor
  · rintro ⟨xs',ys',hxs,hys,_,horder⟩
    have hx : xs = xs' := encodedLists_injective d hxs
    have hy : ys = ys' := encodedLists_injective d hys
    cases hx
    cases hy
    exact horder
  · intro horder
    exact ⟨xs,ys,rfl,rfl,hbounded,horder⟩

private theorem paddedBoundedPair {d : Nat} (weak : Bool)
    (u v : Expr (Fin d)) (hu : u.depth ≤ 2) (hv : v.depth ≤ 2) :
    BoundedSourcePair (left u v) (if weak then weakRight u v else strictRight u v) := by
  obtain ⟨hleft,hweak,hstrict,bleft,bweak,bstrict⟩ :=
    WWBoundedVectorPaddingProof.originalBoundedVectors d u v hu hv
  have dleft : HigherDepthTwo (left u v) := by
    refine ⟨rfl,.add v .one,?_,rfl⟩
    simpa [Expr.depth] using hv
  have dweak : HigherDepthTwo (weakRight u v) := ⟨rfl,u,hu,rfl⟩
  have dstrict : HigherDepthTwo (strictRight u v) := ⟨rfl,u,hu,rfl⟩
  cases weak with
  | false => exact ⟨hleft,hstrict,bleft,bstrict,dleft,dstrict⟩
  | true => exact ⟨hleft,hweak,bleft,bweak,dleft,dweak⟩

/-- The source strict scalar comparison V<U is the same positive-integer
condition as V+1<=U. The original padding realizes this condition with weak
vector comparison and with strict-at-zero WW vector comparison separately. -/
private theorem paddedSourceReduction {d : Nat} (weak : Bool)
    (u v : Expr (Fin d)) (hu : u.depth ≤ 2) (hv : v.depth ≤ 2) :
    VectorDomain (paddedRaw weak u v) ∧
      (SourceOrder false false v u ↔ VectorComparison weak (paddedRaw weak u v)) := by
  have hbounded := paddedBoundedPair weak u v hu hv
  have hscalar : SourceOrder false false v u ↔
      ∀ ρ : Fin d → PosNat, v.eval ρ < u.eval ρ := by
    simpa only [Bool.false_eq_true,↓reduceIte] using
      ScalarSemanticProof.sourceOrder_iff false false v u
  have hinteger : (∀ ρ : Fin d → PosNat, v.eval ρ < u.eval ρ) ↔
      ∀ ρ : Fin d → PosNat, v.eval ρ + 1 ≤ u.eval ρ := by
    constructor <;> intro h ρ <;> have hh := h ρ <;> omega
  have hpadded :
      (if weak then VectorLE (left u v) (if weak then weakRight u v else strictRight u v)
        else VectorLT (left u v) (if weak then weakRight u v else strictRight u v)) ↔
      ∀ ρ : Fin d → PosNat, v.eval ρ + 1 ≤ u.eval ρ := by
    cases weak with
    | false => exact (WWBoundedVectorPaddingProof.exactComparisonReduction d u v hu hv).2
    | true => exact (WWBoundedVectorPaddingProof.exactComparisonReduction d u v hu hv).1
  refine ⟨⟨left u v,(if weak then weakRight u v else strictRight u v),
    rfl,rfl,hbounded⟩,?_⟩
  exact hscalar.trans (hinteger.trans
    (hpadded.symm.trans (vectorComparison_vectorCode weak (left u v)
      (if weak then weakRight u v else strictRight u v) hbounded).symm))

/-- Every RE complement is reduced by the actual polynomial compiler and
the literal two-component padding program. All output certificates hold
uniformly, independently of whether the source input belongs to the set. -/
theorem vectorHardness : Targets.VectorHardness := by
  intro weak P hP
  obtain ⟨m,p,_,_,hwell,hcompute,hcode,hroot⟩ :=
    MRDPFamilyProof.rePolynomialFamily P hP
  refine ⟨fun x => vectorProgram weak (specializationCode p x),
    (ProgramsProof.vectorPrograms weak).comp hcompute,?_⟩
  intro x
  change VectorDomain (vectorProgram weak (specializationCode p x)) ∧
    (¬ P x ↔ VectorComparison weak (vectorProgram weak (specializationCode p x)))
  let q := specialize x p
  have hbridge := ScalarSemanticProof.polynomialSourceBridge q (hwell x) false
  obtain ⟨v,u,hvcode,hucode,hv,hu⟩ := hbridge.1
  have hraw : polynomialRaw false q = expressionCode v u := by
    apply Prod.ext
    · rfl
    · exact Prod.ext hvcode hucode
  have hscalar : scalarProgram false (specializationCode p x) = expressionCode v u := by
    calc
      scalarProgram false (specializationCode p x) =
          scalarProgram false (Encodable.encode (PolynomialCircuit.encode q)) :=
        congrArg (scalarProgram false) (hcode x)
      _ = polynomialRaw false q := ProgramsProof.scalarCalibration false q
      _ = expressionCode v u := hraw
  rw [ProgramsProof.vectorCalibration weak (specializationCode p x)
    (NonnegativePolynomialComparison.bound q) u v hu hv hscalar]
  have hpadded := paddedSourceReduction weak u v hu hv
  refine ⟨hpadded.1,?_⟩
  calc
    ¬ P x ↔ ¬ PolynomialDomainShift.HasNonnegativeRoot q := not_congr (hroot x)
    _ ↔ ScalarComparison false false (polynomialRaw false q) := hbridge.2 false
    _ ↔ SourceOrder false false v u :=
      (iff_of_eq (congrArg (ScalarComparison false false) hraw)).trans
        (ScalarSemanticProof.scalarComparison_expressionCode false false v u hv hu)
    _ ↔ VectorComparison weak (paddedRaw weak u v) := hpadded.2

/-- A putative decider is queried only on the uniformly certified genuine
bounded vectors. Its answers on all other inputs play no role in the pullback. -/
theorem vectorUndecidable : Targets.VectorUndecidable := by
  intro weak hdecider
  obtain ⟨answer,hanswer,hcorrect⟩ := hdecider
  obtain ⟨reduce,hcompute,hreduce⟩ := vectorHardness weak
    DiophantineCompletion.Undecidability.natHaltsZero
    MRDPFamilyProof.haltingObstruction.1
  have hbool : Computable (fun e => answer (reduce e)) := hanswer.comp hcompute
  have hmeaning : ∀ e,
      ¬ DiophantineCompletion.Undecidability.natHaltsZero e ↔ answer (reduce e) = true := by
    intro e
    exact (hreduce e).2.trans (hcorrect (reduce e) (hreduce e).1).symm
  have hcomplement : ComputablePred
      (fun e => ¬ DiophantineCompletion.Undecidability.natHaltsZero e) := by
    apply ComputablePred.computable_iff.mpr
    refine ⟨(fun e => answer (reduce e)),hbool,?_⟩
    exact funext (fun e => propext (hmeaning e))
  exact MRDPFamilyProof.haltingObstruction.2
    (hcomplement.not.of_eq (fun e => by simp))

/-- Whole paper02 thm:bounded-bare-vectors: both original orders are
undecidable on computably generated bounded C-vectors of exactly two
components, with the finite depth-two expression retained above component zero. -/
theorem fullBoundedBareVectors : Targets.FullBoundedBareVectors :=
  ⟨vectorHardness,vectorUndecidable⟩

end LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.VectorProof
