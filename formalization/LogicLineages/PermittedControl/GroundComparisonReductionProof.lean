module
public import LogicLineages.PermittedControl.GroundComparisonReductionTargets
import LogicLineages.PermittedControl.GroundComparisonDomainProof
import LogicLineages.PermittedControl.GroundComparisonPositiveProof

public section
namespace LogicLineages.PermittedControl.GroundComparisonReduction
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax Source.ForwardTranslation
open SelectedSourceDomain SelectedGeneratedSource
open GroundComparison (Relation Canonical Holds vectorAt)
open GroundComparisonPositive (positiveTest paddedValue exactPositiveTest)
open GroundScalarCircuit (Counter)

private theorem variable_ground {Γ : List Ty} {τ : Ty} (x : Variable Γ τ)
    (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) : τ=Ty.ground := by
  induction x with
  | here => exact hΓ _ (by simp)
  | there x ih => exact ih (fun σ h => hΓ σ (by simp [h]))

private theorem index_inj {Γ : List Ty} {τ : Ty} (v w : Variable Γ τ)
    (h : SourceTypedPorts.variableIndex v = SourceTypedPorts.variableIndex w) : v = w := by
  induction v with
  | here => cases w <;> simp_all [SourceTypedPorts.variableIndex]
  | there v ih =>
      cases w with
      | here => simp [SourceTypedPorts.variableIndex] at h
      | there w => exact congrArg Variable.there (ih w (Nat.succ.inj h))

private theorem idx_inj {Γ : List Ty} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (c d : OrdinalComponent Γ)
    (h : idx c = idx d) : c = d := by
  rcases c with ⟨σ,x,j⟩
  rcases d with ⟨σ',y,k⟩
  have hσ := variable_ground x hΓ
  have hσ' := variable_ground y hΓ
  subst hσ
  subst hσ'
  have hxy : x = y := index_inj x y h
  subst hxy
  have hjk : j = k := by
    apply Fin.ext
    have hj := j.isLt
    have hk := k.isLt
    change j.val < 1 at hj
    change k.val < 1 at hk
    omega
  subst hjk
  rfl

/-- Coordinates of an assigned vector at a substitution whose valuation is `ρ`. -/
private theorem vecAt (ctrl : Nat → Nat) {Γ : List Ty} {n : Nat} (v : OrdinalVector Γ n)
    (c : CompiledVector (OrdinalComponent Γ) n)
    (hv : ∀ ρ : OrdinalComponent Γ → Nat, ∀ j,
      vectorValueWith ctrl c ρ j = ParametricSourceSuccessor.denoteWith ctrl (fun x => (ρ x : Ordinal)) (v j))
    (s : AdmissibleSubstitution ctrl Γ) (ρ : OrdinalComponent Γ → Nat)
    (hs : ∀ x, valuation ctrl s x = (ρ x : Ordinal)) :
    vectorAt ctrl v s 0 = ((scalarValueWith ctrl ρ c.scalar : Nat) : Ordinal) ∧
      ∀ k, vectorAt ctrl v s (k+1) = paddedValue (List.ofFn c.positive) k := by
  have hval : valuation ctrl s = fun x => (ρ x : Ordinal) := funext hs
  have he : ∀ j, expressionValue ctrl s (v j) = vectorValueWith ctrl c ρ j := by
    intro j
    rw [hv]
    unfold expressionValue
    rw [hval]
  constructor
  · unfold vectorAt
    rw [dif_pos (Nat.succ_pos n),he]
    rfl
  · intro k
    unfold vectorAt
    by_cases hk : k+1 < n+1
    · rw [dif_pos hk,he]
      have hfin : (⟨k+1,hk⟩ : Fin (n+1)) = Fin.succ ⟨k,by omega⟩ := rfl
      rw [hfin]
      unfold vectorValueWith
      rw [Fin.cases_succ]
      unfold paddedValue
      rw [List.map_ofFn,List.getD_eq_getElem _ _ (by simp; omega),List.getElem_ofFn]
      rfl
    · rw [dif_neg hk]
      unfold paddedValue
      rw [List.getD_eq_default _ _ (by simp; omega)]

/-- From positive valuations of components to positive valuations of shared indices. -/
private theorem toIndex {Γ : List Ty} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground)
    (Q : (OrdinalComponent Γ → Nat) → Prop) :
    (∀ ρ : OrdinalComponent Γ → Nat, (∀ x, 0 < ρ x) → Q ρ) ↔
      ∀ ν : Nat → Nat, (∀ n, 0 < ν n) → Q (fun x => ν (idx x)) := by
  classical
  constructor
  · intro h ν hν
    exact h _ (fun x => hν _)
  · intro h ρ hρ
    let ν : Nat → Nat := fun n => if hn : ∃ c : OrdinalComponent Γ, idx c = n then ρ (Classical.choose hn) else 1
    have hν : ∀ n, 0 < ν n := by
      intro n
      by_cases hn : ∃ c : OrdinalComponent Γ, idx c = n
      · simp only [ν,dif_pos hn]
        exact hρ _
      · simp only [ν,dif_neg hn]
        omega
    have heq : (fun x => ν (idx x)) = ρ := by
      funext x
      have hx : ∃ c : OrdinalComponent Γ, idx c = idx x := ⟨x,rfl⟩
      simp only [ν,dif_pos hx]
      rw [idx_inj hΓ _ _ (Classical.choose_spec hx)]
    have := h ν hν
    rwa [heq] at this

theorem exactCanonicalReduction : ExactCanonicalReduction := by
  intro ctrl K hsel p Γ hΓ τ υ a b va vb ca cb ha hb hva hvb rel
  have dom := GroundComparisonDomain.selectedGroundDomain ctrl K hsel
  have canon : Canonical ctrl p rel a b ↔ Holds ctrl rel va vb := by
    constructor
    · rintro ⟨av,bv,h1,h2,h⟩
      rw [ha] at h1
      rw [hb] at h2
      obtain rfl := Option.some.inj h1
      obtain rfl := Option.some.inj h2
      exact h
    · intro h
      exact ⟨va,vb,ha,hb,h⟩
  rw [canon]
  -- abbreviations
  let SA : (OrdinalComponent Γ → Nat) → Nat := fun ρ => scalarValueWith ctrl ρ ca.scalar
  let SB : (OrdinalComponent Γ → Nat) → Nat := fun ρ => scalarValueWith ctrl ρ cb.scalar
  let PA := paddedValue (List.ofFn ca.positive)
  let PB := paddedValue (List.ofFn cb.positive)
  -- one admissible substitution exists
  obtain ⟨s₁,hs₁⟩ := dom.1 Γ hΓ (fun _ => 1) (fun _ => Nat.one_pos)
  -- every substitution comes from a positive valuation and conversely
  have atS : ∀ s : AdmissibleSubstitution ctrl Γ, ∃ ρ : OrdinalComponent Γ → Nat, (∀ x, 0 < ρ x) ∧
      vectorAt ctrl va s 0 = (SA ρ : Ordinal) ∧ vectorAt ctrl vb s 0 = (SB ρ : Ordinal) ∧
      (∀ k, vectorAt ctrl va s (k+1) = PA k) ∧ (∀ k, vectorAt ctrl vb s (k+1) = PB k) := by
    intro s
    obtain ⟨ρ,hρ,hs⟩ := dom.2 Γ hΓ s
    exact ⟨ρ,hρ,(vecAt ctrl va ca hva s ρ hs).1,(vecAt ctrl vb cb hvb s ρ hs).1,
      (vecAt ctrl va ca hva s ρ hs).2,(vecAt ctrl vb cb hvb s ρ hs).2⟩
  have atR : ∀ ρ : OrdinalComponent Γ → Nat, (∀ x, 0 < ρ x) → ∃ s : AdmissibleSubstitution ctrl Γ,
      vectorAt ctrl va s 0 = (SA ρ : Ordinal) ∧ vectorAt ctrl vb s 0 = (SB ρ : Ordinal) := by
    intro ρ hρ
    obtain ⟨s,hs⟩ := dom.1 Γ hΓ ρ hρ
    exact ⟨s,(vecAt ctrl va ca hva s ρ hs).1,(vecAt ctrl vb cb hvb s ρ hs).1⟩
  have pa₁ : ∀ k, vectorAt ctrl va s₁ (k+1) = PA k := (vecAt ctrl va ca hva s₁ _ hs₁).2
  have pb₁ : ∀ k, vectorAt ctrl vb s₁ (k+1) = PB k := (vecAt ctrl vb cb hvb s₁ _ hs₁).2
  have pos := exactPositiveTest (equalFlag rel) (List.ofFn ca.positive) (List.ofFn cb.positive)
  have noCounter : ∀ (R : Nat → Nat → Prop),
      (¬ ∃ ν : Nat → Nat, (∀ n, 0 < ν n) ∧ R (SA (fun x => ν (idx x))) (SB (fun x => ν (idx x)))) ↔
        ∀ ρ : OrdinalComponent Γ → Nat, (∀ x, 0 < ρ x) → ¬ R (SA ρ) (SB ρ) := by
    intro R
    rw [toIndex hΓ (fun ρ => ¬ R (SA ρ) (SB ρ))]
    constructor
    · intro h ν hν hr
      exact h ⟨ν,hν,hr⟩
    · rintro h ⟨ν,hν,hr⟩
      exact h ν hν hr
  cases rel with
  | weak =>
    change _ ↔ _ ∧ ¬ ∃ ν : Nat → Nat, (∀ n, 0 < ν n) ∧ Counter 0 _ _
    simp only [Counter,if_pos] at noCounter ⊢
    rw [noCounter (fun x y => y < x),pos]
    simp only [equalFlag,Bool.false_eq_true,if_false]
    constructor
    · intro h
      refine ⟨fun k => ?_,fun ρ hρ => ?_⟩
      · have := h s₁ (k+1)
        rwa [pa₁,pb₁] at this
      · obtain ⟨s,e1,e2⟩ := atR ρ hρ
        have := h s 0
        rw [e1,e2] at this
        exact not_lt.2 (by exact_mod_cast this)
    · rintro ⟨hp,hs⟩ s j
      obtain ⟨ρ,hρ,e1,e2,e3,e4⟩ := atS s
      cases j with
      | zero =>
        rw [e1,e2]
        exact_mod_cast not_lt.1 (hs ρ hρ)
      | succ k =>
        rw [e3,e4]
        exact hp k
  | strict =>
    change _ ↔ _ ∧ ¬ ∃ ν : Nat → Nat, (∀ n, 0 < ν n) ∧ Counter 1 _ _
    simp only [Counter,one_ne_zero,if_false,if_true] at noCounter ⊢
    rw [noCounter (fun x y => y ≤ x),pos]
    simp only [equalFlag,Bool.false_eq_true,if_false]
    constructor
    · rintro ⟨h0,hj⟩
      refine ⟨fun k => ?_,fun ρ hρ => ?_⟩
      · have := hj s₁ (k+1) (Nat.succ_pos k)
        rwa [pa₁,pb₁] at this
      · obtain ⟨s,e1,e2⟩ := atR ρ hρ
        have := h0 s
        rw [e1,e2] at this
        exact not_le.2 (by exact_mod_cast this)
    · rintro ⟨hp,hs⟩
      constructor
      · intro s
        obtain ⟨ρ,hρ,e1,e2,_,_⟩ := atS s
        rw [e1,e2]
        exact_mod_cast not_le.1 (hs ρ hρ)
      · intro s j hj
        obtain ⟨ρ,hρ,_,_,e3,e4⟩ := atS s
        obtain ⟨k,rfl⟩ : ∃ k, j = k+1 := ⟨j-1,by omega⟩
        rw [e3,e4]
        exact hp k
  | equal =>
    change _ ↔ _ ∧ ¬ ∃ ν : Nat → Nat, (∀ n, 0 < ν n) ∧ Counter 2 _ _
    simp only [Counter,show (2 : Nat) ≠ 0 by decide,show (2 : Nat) ≠ 1 by decide,if_false] at noCounter ⊢
    rw [noCounter (fun x y => x ≠ y),pos]
    simp only [equalFlag,if_true]
    constructor
    · intro h
      refine ⟨fun k => ?_,fun ρ hρ => ?_⟩
      · have := h s₁ (k+1)
        rwa [pa₁,pb₁] at this
      · obtain ⟨s,e1,e2⟩ := atR ρ hρ
        have := h s 0
        rw [e1,e2] at this
        exact not_not.2 (by exact_mod_cast this)
    · rintro ⟨hp,hs⟩ s j
      obtain ⟨ρ,hρ,e1,e2,e3,e4⟩ := atS s
      cases j with
      | zero =>
        rw [e1,e2]
        exact_mod_cast not_not.1 (hs ρ hρ)
      | succ k =>
        rw [e3,e4]
        exact hp k

#print axioms exactCanonicalReduction
end LogicLineages.PermittedControl.GroundComparisonReduction
