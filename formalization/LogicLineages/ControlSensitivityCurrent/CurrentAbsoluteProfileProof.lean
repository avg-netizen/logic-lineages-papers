module
public import LogicLineages.ControlSensitivityCurrent.CurrentAbsoluteAnchorProof
public import LogicLineages.PermittedControl.SelectedHardnessScalarSyntaxProof
public import LogicLineages.OrdinalComparison.GeneralOmegaHeadLimitProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentAbsolute

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.PermittedControl
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
open ParametricSourceSuccessor AdmissibleAssignment
open SelectedHardnessUnusedProof (unusedVector freePart)

theorem closed_value (f : Nat → Nat) {Γ} (e : OrdinalExpression Γ) (he : ordinalExpressionVariables e = [])
    (ν μ : OrdinalComponent Γ → Ordinal) : denoteWith f ν e = denoteWith f μ e := by
  induction e with
  | var c => simp [ordinalExpressionVariables] at he
  | zero | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    obtain ⟨ha,hb⟩ := List.append_eq_nil_iff.mp he
    simp only [denoteWith, iha ha, ihb hb]

theorem positive_congr (f : Nat → Nat) {Γ m} (ν : OrdinalComponent Γ → Ordinal)
    (v w : OrdinalVector Γ m) (h : ∀ j, 0 < j.val → denoteWith f ν (v j) = denoteWith f ν (w j))
    (j : Nat) (hj : 0 < j) :
    denoteWith f ν (ordinalVectorAt v j) = denoteWith f ν (ordinalVectorAt w j) := by
  unfold ordinalVectorAt
  split_ifs
  · exact h _ hj
  · rfl

theorem box_head_congr (f : Nat → Nat) {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (n : Nat) (a b c d : Nat → OrdinalExpression Γ)
    (ha : ∀ j, 0 < j → denoteWith f ν (a j) = denoteWith f ν (c j))
    (hb : ∀ j, 0 < j → denoteWith f ν (b j) = denoteWith f ν (d j))
    (j : Nat) (hj : 0 < j) :
    denoteWith f ν (ordinalBoxPositive n a b j) = denoteWith f ν (ordinalBoxPositive n c d j) := by
  conv_lhs => rw [ordinalBoxPositive]
  conv_rhs => rw [ordinalBoxPositive]
  by_cases hn : j ≤ n
  · simp only [hn, ↓reduceDIte, denoteWith]
    rw [box_head_congr f ν n a b c d ha hb (j+1) (by omega), ha j hj, hb j hj]
  · simpa only [hn, ↓reduceDIte] using ha j hj
termination_by n+1-j
decreasing_by omega

theorem unused_positive (f : Nat → Nat) (p : AdmissibleSum.Policy) {Γ m} (ν : OrdinalComponent Γ → Ordinal)
    (v w : OrdinalVector Γ m) (h : ∀ j, 0 < j.val → denoteWith f ν (v j) = denoteWith f ν (w j))
    (j : Fin (max 1 m + 1)) (hj : 0 < j.val) :
    denoteWith f ν (unusedVector p v j) = denoteWith f ν (unusedVector p w j) := by
  have hd (hj2 : j.val < 2) :
      denoteWith f ν (AdmissibleSum.expand (p.shape .positiveAbstraction m)
        (fun i => freePart v i ⟨j.val,hj2⟩)) =
      denoteWith f ν (AdmissibleSum.expand (p.shape .positiveAbstraction m)
        (fun i => freePart w i ⟨j.val,hj2⟩)) := by
    rw [SelectedSumValueProof.expand_value, SelectedSumValueProof.expand_value]
    simp only [List.map_ofFn, Function.comp_def]
    congr 1
    rw [List.ofFn_inj]
    funext i
    unfold freePart
    split_ifs with he
    · change i.val = j.val at he
      have hi : 0 < i.val := he.symm ▸ hj
      simp only [denoteWith, h i hi]
    · rfl
  have hj0 : j.val ≠ 0 := Nat.ne_of_gt hj
  by_cases hj2 : j.val < 2
  · by_cases hm : j.val < m+1
    · simp only [unusedVector, hj0, hj2, hm, ↓reduceIte, ↓reduceDIte, denoteWith]
      rw [hd, h _ hj]
    · simpa only [unusedVector, hj0, hj2, hm, ↓reduceIte, ↓reduceDIte] using hd hj2
  · have hm : j.val < m+1 := by have := j.isLt; omega
    simp only [unusedVector, hj0, hj2, hm, ↓reduceIte, ↓reduceDIte, denoteWith]
    rw [h _ hj]

theorem ground_app_positive (f : Nat → Nat) (p : AdmissibleSum.Policy) {Γ τ}
    (ν : OrdinalComponent Γ → Ordinal) (u : OrdinalVector Γ (max 1 τ.level)) (g : OrdinalVector Γ 0)
    (j : Fin (τ.level+1)) (hj : 0 < j.val) :
    denoteWith f ν (application (σ := .ground) (τ := τ) p u g j) =
      denoteWith f ν (u ⟨j.val, by have := j.isLt; omega⟩) := by
  simp only [application, box, Ty.level, show j.val ≠ 0 from Nat.ne_of_gt hj, ↓reduceIte]
  rw [ordinalBoxPositive]
  simp only [show ¬j.val ≤ 0 by omega, ↓reduceDIte, ordinalVectorAt]
  simp only [show j.val < max 1 τ.level+1 by have := j.isLt; omega, ↓reduceDIte]

theorem unused_scalar (f : Nat → Nat) (p : AdmissibleSum.Policy) {Γ τ}
    (ν : OrdinalComponent Γ → Ordinal) (v : OrdinalVector Γ τ.level) (n : Nat)
    (hn : denoteWith f ν (v 0) = (n : Ordinal)) :
    denoteWith f ν (unusedVector p v 0) =
      ((AbsoluteObserver.factor τ*n + (AbsoluteObserver.factor τ-1) : Nat) : Ordinal) := by
  let k := 2*(τ.level+1)
  have h : denoteWith f ν (.add (v 0) .one) = ((n+1 : Nat) : Ordinal) := by
    simpa only [denoteWith, hn, Nat.cast_one] using naturalSum_finite n 1
  change ordinalNaturalSum (denoteWith f ν (repeated p .scalarRepeat k (.add (v 0) .one)))
    (denoteWith f ν (v 0)) = _
  rw [SelectedHardnessScalarSyntaxProof.repeated_value f p ν k (n+1) _ h, hn, naturalSum_finite]
  congr 1
  unfold AbsoluteObserver.factor
  rw [Nat.add_sub_cancel]
  change k*(n+1)+n = (k+1)*n+k
  ring

private theorem numeral_value (f : Nat → Nat) (p : AdmissibleSum.Policy) {Γ}
    (ν : OrdinalComponent Γ → Ordinal) (n : Nat) :
    denoteWith f ν (numeral p n) = (n : Ordinal) := by
  cases n with
  | zero => simp [numeral,repeated,denoteWith]
  | succ n =>
    simp only [numeral,repeated]
    rw [SelectedSumValueProof.expand_value]
    simp only [List.ofFn_const,List.map_replicate,denoteWith]
    simpa only [Nat.mul_one, Nat.cast_one] using SelectedHardnessScalarSyntaxProof.values_repeat (n+1) 1

theorem box_tail_value (f : Nat → Nat) (p : AdmissibleSum.Policy) {Γ}
    (ν : OrdinalComponent Γ → Ordinal) (k n m : Nat) (a b : OrdinalExpression Γ)
    (ha : denoteWith f ν a = (n : Ordinal)) (hb : denoteWith f ν b = (m : Ordinal)) :
    denoteWith f ν (boxTail p k a b) = ((n+m+k : Nat) : Ordinal) := by
  unfold boxTail
  by_cases hk : k = 0
  · simp only [hk, ↓reduceIte, denoteWith, ha, hb, naturalSum_finite, Nat.add_zero]
  · simp only [hk, if_false, AdmissiblePartial.three]
    rw [SelectedSumValueProof.expand_value]
    simp only [List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, List.map_cons,
      List.map_nil, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte, ha, hb, numeral_value,
      SelectedSumValueProof.values, List.foldr_cons, List.foldr_nil]
    rw [show ordinalNaturalSum (k : Ordinal) 0 = (k : Ordinal) by
      simpa only [Nat.add_zero, Nat.cast_zero] using naturalSum_finite k 0,
      naturalSum_finite, naturalSum_finite, Nat.add_assoc]

theorem collapse_cancel (f : Nat → Nat) (hf : FullAddition.Targets.SourceGrowth f) {Γ}
    (ρ : OrdinalComponent Γ → Nat) (a b d e : OrdinalExpression Γ)
    (ga : GeneratedOrdinalGrade Γ 1 a)
    (hab : denoteWith f (fun c => ((ρ c+1 : Nat) : Ordinal)) a =
      denoteWith f (fun c => ((ρ c+1 : Nat) : Ordinal)) b)
    (n m : Nat) (hd : denoteWith f (fun c => ((ρ c+1 : Nat) : Ordinal)) d = (n : Ordinal))
    (he : denoteWith f (fun c => ((ρ c+1 : Nat) : Ordinal)) e = (m : Ordinal)) :
    denoteWith f (fun c => ((ρ c+1 : Nat) : Ordinal)) (.collapse a d) =
      denoteWith f (fun c => ((ρ c+1 : Nat) : Ordinal)) (.collapse b e) ↔ n = m := by
  let ν : OrdinalComponent Γ → Ordinal := fun c => ((ρ c+1 : Nat) : Ordinal)
  let u := denoteWith f ν a
  let l := ordinalNaturalProduct Ordinal.omega0 u
  have hl : l < epsilonZero :=
    (GeneralOmegaHeadLimit.Proof.generalPositiveLimit u
      (GenericScalar.generatedPositiveFinite f Γ ρ _ _ ga).1
      (GenericScalar.belowEpsilon f Γ ρ a)).2.2
  have hmono : StrictMono (fun k : Nat => ParametricActualCollapse.collapseWith f (l + (k : Ordinal))) := by
    intro x y hxy
    have hx := actualFiniteTailClosureNorm l hl x
    have hy := actualFiniteTailClosureNorm l hl y
    apply (ParametricActualCollapse.Proof.equation f _ hy.1).1
    · apply (add_lt_add_iff_left l).mpr
      exact_mod_cast hxy
    · rw [hx.2, hy.2]
      exact (Nat.add_le_add_left hxy.le _).trans
        ((self_lt_Phi _).le.trans (hf.1 _))
  simp only [denoteWith, hd, he, ← hab]
  rw [actualNaturalSumFiniteRight _ n, actualNaturalSumFiniteRight _ m]
  constructor
  · intro h
    apply hmono.injective
    exact_mod_cast h
  · rintro rfl
    rfl

end LogicLineages.ControlSensitivityCurrent.CurrentAbsolute
