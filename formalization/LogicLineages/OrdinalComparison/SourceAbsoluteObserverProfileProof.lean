module
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverUnusedProof
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverAnchorProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AbsoluteObserver.Proof
open AdmissibleAssignment
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem rename_value {Γ Δ} (r : Renaming Γ Δ) (t : OrdinalExpression Γ)
    (ν : OrdinalComponent Δ → Ordinal) :
    denote ν (ordinalExpressionRename r t) = denote (fun c => ν (ordinalComponentRename r c)) t := by
  induction t with
  | var c => rfl
  | zero | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    simp only [ordinalExpressionRename, substitute, denote] at *
    rw [iha, ihb]

theorem closed_value {Γ} (t : OrdinalExpression Γ) (ht : ordinalExpressionVariables t = [])
    (ν μ : OrdinalComponent Γ → Ordinal) : denote ν t = denote μ t := by
  induction t with
  | var c => simp [ordinalExpressionVariables] at ht
  | zero | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    obtain ⟨ha, hb⟩ := List.append_eq_nil_iff.mp ht
    simp only [denote, iha ha, ihb hb]

theorem freePart_positive_congr {Γ m} (ν : OrdinalComponent Γ → Ordinal)
    (v w : OrdinalVector Γ m) (h : ∀ j, 0 < j.val → denote ν (v j) = denote ν (w j))
    (i : Fin (m+1)) (j : Fin 2) (hj : 0 < j.val) :
    denote ν (freePart v i j) = denote ν (freePart w i j) := by
  unfold freePart
  split_ifs with he
  · simp only [denote, h i (by omega)]
  · rfl

theorem unused_positive_congr {Γ m} (ν : OrdinalComponent Γ → Ordinal)
    (v w : OrdinalVector Γ m) (h : ∀ j, 0 < j.val → denote ν (v j) = denote ν (w j))
    (j : Fin (max 1 m + 1)) (hj : 0 < j.val) :
    denote ν (unusedVector v j) = denote ν (unusedVector w j) := by
  have hj0 : j.val ≠ 0 := Nat.ne_of_gt hj
  have he (hj2 : j.val < 2) :
      denote ν (AdmissibleSum.expand (OrdinalSyntax.defaultPolicy.shape .positiveAbstraction m)
        (fun i => freePart v i ⟨j.val,hj2⟩)) =
      denote ν (AdmissibleSum.expand (OrdinalSyntax.defaultPolicy.shape .positiveAbstraction m)
        (fun i => freePart w i ⟨j.val,hj2⟩)) := by
    apply AdmissibleSum.expand_value_congr
    intro i
    exact freePart_positive_congr ν v w h i _ hj
  by_cases hj2 : j.val < 2
  · by_cases hjm : j.val < m+1
    · simp only [unusedVector, hj0, hj2, hjm, ↓reduceIte, ↓reduceDIte, denote]
      rw [he, h _ hj]
    · simpa only [unusedVector, hj0, hj2, hjm, ↓reduceIte, ↓reduceDIte] using he hj2
  · have hjm : j.val < m+1 := by have := j.isLt; omega
    simp only [unusedVector, hj0, hj2, hjm, ↓reduceIte, ↓reduceDIte, denote]
    rw [h _ hj]

theorem vectorAt_positive_congr {Γ m} (ν : OrdinalComponent Γ → Ordinal)
    (v w : OrdinalVector Γ m) (h : ∀ j, 0 < j.val → denote ν (v j) = denote ν (w j))
    (i : Nat) (hi : 0 < i) : denote ν (ordinalVectorAt v i) = denote ν (ordinalVectorAt w i) := by
  unfold ordinalVectorAt
  split_ifs with hm
  · exact h _ hi
  · rfl

theorem box_positive_congr {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (n : Nat) (f g f' g' : Nat → OrdinalExpression Γ)
    (hf : ∀ i, 0 < i → denote ν (f i) = denote ν (f' i))
    (hg : ∀ i, 0 < i → denote ν (g i) = denote ν (g' i)) (i : Nat) (hi : 0 < i) :
    denote ν (ordinalBoxPositive n f g i) = denote ν (ordinalBoxPositive n f' g' i) := by
  conv_lhs => rw [ordinalBoxPositive]
  conv_rhs => rw [ordinalBoxPositive]
  by_cases hin : i ≤ n
  · simp only [hin, ↓reduceDIte, denote]
    rw [box_positive_congr ν n f g f' g' hf hg (i+1) (by omega), hf i hi, hg i hi]
  · simpa only [hin, ↓reduceDIte] using hf i hi
termination_by n+1-i
decreasing_by omega

theorem ground_application_positive {Γ τ} (ν : OrdinalComponent Γ → Ordinal)
    (u : OrdinalVector Γ (max 1 τ.level)) (g : OrdinalVector Γ 0)
    (j : Fin (τ.level+1)) (hj : 0 < j.val) :
    denote ν (application (σ := .ground) (τ := τ) OrdinalSyntax.defaultPolicy u g j) =
      denote ν (u ⟨j.val, by have := j.isLt; omega⟩) := by
  simp only [application, box, Ty.level, show j.val ≠ 0 from Nat.ne_of_gt hj, ↓reduceIte]
  rw [ordinalBoxPositive]
  simp only [show ¬j.val ≤ 0 by omega, ↓reduceDIte, ordinalVectorAt]
  simp only [show j.val < max 1 τ.level+1 by have := j.isLt; omega, ↓reduceDIte]
end LogicLineages.OrdinalComparison.Source.AbsoluteObserver.Proof
