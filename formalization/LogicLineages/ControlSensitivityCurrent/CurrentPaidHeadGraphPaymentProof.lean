module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphOmegaProof
public import LogicLineages.ControlSensitivityCurrent.CurrentAbsoluteProfileProof
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentProof
public import LogicLineages.OrdinalComparison.WWCanonicalBoxProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open AdmissibleSum AdmissibleAssignment ParametricSourceSuccessor
open CurrentUnaryChain (commonUnits)

private theorem unitRead {Γ : List Ty} (ρ : Variable Γ .ground → Nat) :
    (fun x => ((ExistentialPlan.inputs ρ x+1 : Nat) : Ordinal)) = commonUnits ρ := by
  funext x
  rcases x with ⟨σ,x,j⟩
  cases σ <;> rfl

theorem scalarWithAssignment (p : Policy) (f : Nat → Nat) {Γ τ}
    (ρ : Variable Γ .ground → Nat) (a : OriginalTerm Γ τ) (u : OrdinalVector Γ τ.level)
    (hu : assignment p a = some u) (v : Nat) :
    CurrentAbsolute.Scalar p f (ExistentialPlan.inputs ρ) a v ↔
      denoteWith f (commonUnits ρ) (u 0) = (v : Ordinal) := by
  unfold CurrentAbsolute.Scalar
  rw [unitRead]
  constructor
  · rintro ⟨w,hw,h⟩
    cases Option.some.inj (hu.symm.trans hw)
    exact h
  · exact fun h => ⟨u,hu,h⟩

theorem generatedAt (p : Policy) {Γ τ} (a : OriginalTerm Γ τ)
    (u : OrdinalVector Γ τ.level) (hu : assignment p a = some u) :
    ∀ j, GeneratedOrdinalGrade Γ j.val (u j) := by
  obtain ⟨v,hv,hg⟩ := actualAdmissibleAssignmentGenerated Γ τ p a
  cases Option.some.inj (hu.symm.trans hv)
  exact hg

private theorem valueSupport (f : Nat → Nat) {Γ} (q : OrdinalExpression Γ)
    (ν μ : OrdinalComponent Γ → Ordinal)
    (h : ∀ c ∈ ordinalExpressionVariables q, ν c = μ c) :
    denoteWith f ν q = denoteWith f μ q := by
  induction q with
  | zero | one | omega => rfl
  | var x => exact h x (by simp [ordinalExpressionVariables])
  | add a b ha hb | emul a b ha hb | collapse a b ha hb =>
    simp only [denoteWith]
    rw [ha (fun c hc => h c (List.mem_append_left _ hc)),
      hb (fun c hc => h c (List.mem_append_right _ hc))]

theorem positiveUnits (f : Nat → Nat) {Γ} {i : Nat} (q : OrdinalExpression Γ) (hi : 0<i)
    (hq : GeneratedOrdinalGrade Γ i q) (ρ : Variable Γ .ground → Nat) :
    denoteWith f (commonUnits ρ) q = atUnits f q := by
  apply valueSupport
  intro x hx
  have hm := actualGeneratedComponentIndex Γ i q hq x hx
  rcases x with ⟨σ,x,j⟩
  cases σ with
  | ground =>
    change i ≤ j.val at hm
    have hj : j.val<1 := j.isLt
    omega
  | arrow _ _ => rfl

theorem baseHeadFacts (p : Policy) (f : Nat → Nat) {Γ}
    (K : OriginalTerm Γ (Ty.curriedGround 1)) (u : OrdinalVector Γ 1)
    (hu : assignment p K=some u) :
    let β := ordinalNaturalProduct Ordinal.omega0 (atUnits f (u 1))
    β < epsilonZero ∧ Order.IsSuccLimit β := by
  have hgen := generatedAt p K u hu 1
  have hpos := (GenericScalar.generatedPositiveFinite f Γ (fun _ => 0) 1 (u 1) hgen).1
  have hbound := GenericScalar.belowEpsilon f Γ (fun _ => 0) (u 1)
  exact ⟨FunctionalDetector.Proof.omega_product_below _ hbound,
    FunctionalDetector.Proof.omega_product_limit _ hpos hbound⟩

private theorem boxPositiveGrade (p : Policy) {Γ σ τ}
    (B : OrdinalVector Γ (Ty.arrow σ τ).level) (C : OrdinalVector Γ σ.level)
    (bG : ∀ i, GeneratedOrdinalGrade Γ i.val (B i))
    (cG : ∀ i, GeneratedOrdinalGrade Γ i.val (C i)) (i : Fin ((Ty.arrow σ τ).level+1)) (hi : 0<i.val) :
    GeneratedOrdinalGrade Γ i.val (box p B C i) := by
  have hlevels : σ.level < (Ty.arrow σ τ).level := by simp only [Ty.level]; omega
  have h := actualCanonicalBoxGeneratedGrade Γ _ _ hlevels B C bG cG i
  simpa only [ordinalCanonicalBox,box,if_neg (Nat.ne_of_gt hi)] using h

private theorem firstEquation (p : Policy) {Γ σ τ} (hs : 0<σ.level)
    (B : OrdinalVector Γ (Ty.arrow σ τ).level) (C : OrdinalVector Γ σ.level) :
    box p B C (sourceFirst σ τ) = .emul (box p B C (boxSecond σ τ hs))
      (.add (B (sourceFirst σ τ)) (C (callerFirst σ hs))) := by
  have hlevels : σ.level < (Ty.arrow σ τ).level := by simp only [Ty.level]; omega
  have h := (actualCanonicalBoxEquations Γ _ _ hlevels B C).2.1 (sourceFirst σ τ)
    (by decide) (by change 1 ≤ σ.level; omega)
  have hh : 2 < (Ty.arrow σ τ).level+1 := (boxSecond σ τ hs).isLt
  have hc : 1 < σ.level+1 := (callerFirst σ hs).isLt
  simpa only [sourceFirst,boxSecond,callerFirst,ordinalVectorAt,dif_pos hh,dif_pos hc,
    ordinalCanonicalBox,box,Nat.one_ne_zero,if_false,Nat.reduceAdd,of_decide_eq_false] using h

theorem exactOriginalPayment : Targets.ExactOriginalPayment := by
  intro p f Γ Ξ σ τ B C K b δ h
  have hβ := baseHeadFacts p f K h.Kvector h.assignK
  have hk := GenericScalar.belowEpsilon f Ξ (fun _ => 0) (h.Kvector 1)
  have hp : h.paidHead=shiftHead h.baseHead δ := by
    unfold Paid.paidHead Paid.baseHead
    rw [h.payment]
    exact productOmegaTail _ hk δ
  refine ⟨hβ.1,hβ.2,hp,?_⟩
  intro ρ
  let ν := commonUnits ρ
  have hB := generatedAt p B h.Bvector h.assignB
  have hC := generatedAt p C h.Cvector h.assignC
  let i₂ := boxSecond σ τ h.callerLevel
  let i₁ := sourceFirst σ τ
  have g₂ := boxPositiveGrade p h.Bvector h.Cvector hB hC i₂ (by decide)
  have hb : denoteWith f ν (box p h.Bvector h.Cvector i₂)=(b : Ordinal) :=
    (positiveUnits f _ (by decide) g₂ ρ).trans h.budget
  have hz : (2 : Ordinal)^(b : Ordinal)=((2^b : Nat) : Ordinal) := by
    simpa only [Ordinal.opow_natCast,Nat.cast_ofNat] using (Ordinal.natCast_pow 2 b).symm
  have hfirst := firstEquation p h.callerLevel h.Bvector h.Cvector
  have hval : denoteWith f ν (box p h.Bvector h.Cvector i₁) =
      ordinalNaturalProduct ((2^b : Nat) : Ordinal)
        (ordinalNaturalSum (denoteWith f ν (h.Bvector i₁))
          (denoteWith f ν (h.Cvector (callerFirst σ h.callerLevel)))) := by
    change denoteWith f ν (box p h.Bvector h.Cvector i₁) = _
    rw [hfirst]
    simp only [denoteWith,← show boxSecond σ τ h.callerLevel=i₂ from rfl,hb,hz]
  have hB₁ := positiveUnits f _ (show 0<i₁.val by decide) (hB i₁) ρ
  have hC₁ := positiveUnits f _ (show 0<(callerFirst σ h.callerLevel).val by decide)
    (hC (callerFirst σ h.callerLevel)) ρ
  have hhead : ordinalNaturalProduct Ordinal.omega0 (denoteWith f ν (box p h.Bvector h.Cvector i₁)) = h.paidHead := by
    unfold Paid.paidHead
    rw [hval,hB₁,hC₁]
  refine ⟨hb,hval,?_⟩
  intro B₀ C₀ y hB₀ hC₀
  have hbs := (scalarWithAssignment p f ρ B h.Bvector h.assignB B₀).mp hB₀
  have hcs := (scalarWithAssignment p f ρ C h.Cvector h.assignC C₀).mp hC₀
  let w : OrdinalVector Γ τ.level := application p h.Bvector h.Cvector
  have hw : assignment p (.app B C)=some w := by
    simp only [assignment,h.assignB,h.assignC,Option.bind_some,w]
    rfl
  rw [scalarWithAssignment p f ρ _ w hw]
  have htail := CurrentAbsolute.box_tail_value f p ν σ.level B₀ C₀ (h.Bvector 0) (h.Cvector 0) hbs hcs
  change (ParametricActualCollapse.collapseWith f
      (ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 (denoteWith f ν
        (box p h.Bvector h.Cvector i₁))) (denoteWith f ν (boxTail p σ.level (h.Bvector 0) (h.Cvector 0)))) : Ordinal) =
      (y : Ordinal) ↔ _
  rw [hhead,htail,actualNaturalSumFiniteRight]
  unfold J actualHeadInitial
  have he : actualOrdinalNorm h.paidHead+B₀+C₀+σ.level-actualOrdinalNorm h.paidHead=B₀+C₀+σ.level := by omega
  rw [he]
  exact ⟨fun eq => by exact_mod_cast eq.symm,fun eq => by exact_mod_cast eq.symm⟩

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
