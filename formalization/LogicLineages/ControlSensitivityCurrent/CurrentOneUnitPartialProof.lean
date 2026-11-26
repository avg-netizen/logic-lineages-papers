module
public import LogicLineages.ControlSensitivityCurrent.CurrentOneUnitInflationProof
public import LogicLineages.PermittedControl.SelectedHardnessScalarSyntaxProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentOneUnit

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
open AdmissibleAssignment AdmissibleSum ParametricSourceSuccessor
open OneUnit.Proof (free_add)

private theorem activeThreeValue (p : Policy) (f : Nat → Nat) {Γ : List Ty}
    (ν : OrdinalComponent Γ → Ordinal) (a b c : OrdinalExpression Γ) :
    denoteWith f ν (AdmissiblePartial.three p .activeAdd a b c) =
      ordinalNaturalSum (ordinalNaturalSum (denoteWith f ν a) (denoteWith f ν b))
        (denoteWith f ν c) := by
  unfold AdmissiblePartial.three
  rw [LogicLineages.PermittedControl.SelectedSumValueProof.sum_value f Γ 3
    (p.shape .activeAdd 2) (OrdinalSyntax.leftShape 2) _ ν]
  rfl

private theorem activeAddPartialValue (p : Policy) (f : Nat → Nat)
    {Γ : List Ty} {σ : Ty} (ν : OrdinalComponent Γ → Ordinal)
    (a b : OrdinalExpression (σ :: Γ)) (ha : ordinalHeadFree a = false)
    (pa pb : OrdinalPartialVector Γ σ) (A B : Nat)
    (hpa : AdmissiblePartial.run p 0 a = some pa)
    (hpb : AdmissiblePartial.run p 0 b = some pb)
    (hA : denoteWith f ν (pa 0) = (A : Ordinal))
    (hB : denoteWith f ν (pb 0) = (B : Ordinal)) :
    ∃ v : OrdinalPartialVector Γ σ, AdmissiblePartial.run p 0 (.add a b) = some v ∧
      denoteWith f ν (v 0) = ((A+B+1 : Nat) : Ordinal) := by
  refine ⟨fun j => AdmissiblePartial.three p .activeAdd (pa j) (pb j) .one,?_,?_⟩
  · rw [AdmissiblePartial.run.eq_def,free_add,ha]
    simp only [Bool.false_and,Bool.false_eq_true,↓reduceIte,hpa,hpb,Option.bind_some] <;> rfl
  · rw [activeThreeValue,hA,hB,naturalSum_finite]
    change ordinalNaturalSum ((A+B : Nat) : Ordinal) 1 = _
    simpa only [Nat.cast_one] using naturalSum_finite (A+B) 1

private theorem shapePartialValue (p : Policy) (f : Nat → Nat)
    {Γ : List Ty} {σ : Ty} (ν : OrdinalComponent Γ → Ordinal)
    {n : Nat} (s : Shape n) (e : OrdinalExpression (σ :: Γ))
    (he : ordinalHeadFree e = false) (v : OrdinalPartialVector Γ σ) (P : Nat)
    (hv : AdmissiblePartial.run p 0 e = some v) (hP : denoteWith f ν (v 0) = (P : Ordinal)) :
    ∃ q : OrdinalPartialVector Γ σ, AdmissiblePartial.run p 0 (shapeCopies s e) = some q ∧
      denoteWith f ν (q 0) = ((n*P+(n-1) : Nat) : Ordinal) := by
  induction s with
  | leaf => exact ⟨v,hv,by simpa using hP⟩
  | @join n m a b ia ib =>
    obtain ⟨qa,ha,hqa⟩ := ia
    obtain ⟨qb,hb,hqb⟩ := ib
    have hact := (shapeCopiesActiveSize a e he).1
    obtain ⟨q,hq,heq⟩ := activeAddPartialValue p f ν (shapeCopies a e) (shapeCopies b e)
      hact qa qb _ _ ha hb hqa hqb
    refine ⟨q,hq,heq.trans ?_⟩
    have hn := LogicLineages.ControlSensitivityCurrent.PolicyGadget.smallShapes.1 n a
    have hm := LogicLineages.ControlSensitivityCurrent.PolicyGadget.smallShapes.1 m b
    apply congrArg (fun n : Nat => (n : Ordinal))
    rw [Nat.add_mul]
    omega

theorem inflatedPartialValue (p : Policy) (f : Nat → Nat)
    {Γ : List Ty} {σ τ : Ty} (ν : OrdinalComponent Γ → Ordinal)
    (e : OrdinalExpression (σ :: Γ)) (he : ordinalHeadFree e = false)
    (v : OrdinalPartialVector Γ σ) (P : Nat)
    (hv : AdmissiblePartial.run p 0 e = some v) (hP : denoteWith f ν (v 0) = (P : Ordinal)) :
    ∃ q : OrdinalPartialVector Γ σ, AdmissiblePartial.run p 0 (inflated p τ e) = some q ∧
      denoteWith f ν (q 0) = ((OneUnit.coefficient τ*P+4*OneUnit.copies τ : Nat) : Ordinal) := by
  let k := OneUnit.copies τ
  have hk : 0 < k := by unfold k OneUnit.copies; omega
  let w : OrdinalPartialVector Γ σ := ordinalFreePartialVector 0 .one
  have hw : AdmissiblePartial.run p 0 (.one : OrdinalExpression (σ :: Γ)) = some w := by
    rw [AdmissiblePartial.run.eq_def] <;> rfl
  have hW : denoteWith f ν (w 0) = (2 : Ordinal) := by
    change ordinalNaturalSum 1 1 = (2 : Ordinal)
    simpa using naturalSum_finite 1 1
  obtain ⟨a,ha,hA⟩ := activeAddPartialValue p f ν e .one he v w P 2 hv hw hP hW
  have ha' : ordinalHeadFree (.add e .one) = false := by rw [free_add,he] <;> rfl
  have hshape (i : Nat) (hi : k = i+1) :
      ∃ b : OrdinalPartialVector Γ σ,
        AdmissiblePartial.run p 0 (repeated p .scalarRepeat k (.add e .one)) = some b ∧
        denoteWith f ν (b 0) = ((k*(P+2+1)+(k-1) : Nat) : Ordinal) := by
    rw [hi]
    exact shapePartialValue p f ν (p.shape .scalarRepeat i) (.add e .one) ha' a _ ha hA
  obtain ⟨b,hb,hB⟩ := hshape (k-1) (by omega)
  obtain ⟨hc,_⟩ := repeatedActiveSize p .scalarRepeat k hk (.add e .one) ha'
  obtain ⟨q,hq,hQ⟩ := activeAddPartialValue p f ν (repeated p .scalarRepeat k (.add e .one))
    e hc b v _ _ hb hv hB hP
  refine ⟨q,hq,hQ.trans ?_⟩
  apply congrArg (fun n : Nat => (n : Ordinal))
  change k*(P+2+1)+(k-1)+P+1 = (k+1)*P+4*k
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul]
  omega

end LogicLineages.ControlSensitivityCurrent.CurrentOneUnit
