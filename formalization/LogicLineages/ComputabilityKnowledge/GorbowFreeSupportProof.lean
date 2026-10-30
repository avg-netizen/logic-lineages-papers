module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowFreeSupport
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.GorbowFreeSupportProof
open GorbowSyntax GorbowFreeSupport

theorem unbindMembership : Comparators.GorbowFreeSupport.UnbindMembership := by
  intro s i
  simp only [unbind, Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨j, ⟨hj, hs⟩, he⟩
    have hji : j = i + 1 := by
      change j - 1 = i at he
      omega
    simpa only [hji] using hs
  · intro h
    exact ⟨i + 1, ⟨by omega, h⟩, rfl⟩

private theorem termBound (n : Nat) (t : Term n) : ∀ i ∈ termSupport t, i < n := by
  induction t with
  | var j => intro i hi; have he : i = j.val := Finset.mem_singleton.mp hi; simpa only [he] using j.isLt
  | zero => intro i hi; simp [termSupport] at hi
  | succ t h | universalFunction t h => exact h
  | add t u ht hu | mul t u ht hu =>
      intro i hi
      exact (Finset.mem_union.mp hi).elim (ht i) (hu i)

private theorem formulaBound (n : Nat) (φ : Formula n) : ∀ i ∈ formulaSupport φ, i < n := by
  induction φ with
  | equal t u | knowledge t u =>
      intro i hi
      simp only [formulaSupport, Finset.mem_union] at hi
      exact hi.elim (termBound _ t i) (termBound _ u i)
  | universalRelation t | agent t | knowledgeAll t | truth t => exact termBound _ t
  | neg φ h => exact h
  | imp φ ψ hφ hψ | conj φ ψ hφ hψ | disj φ ψ hφ hψ =>
      intro i hi
      simp only [formulaSupport, Finset.mem_union] at hi
      exact hi.elim (hφ i) (hψ i)
  | all φ h | ex φ h =>
      intro i hi
      have hi' := (unbindMembership (formulaSupport φ) i).mp hi
      have := h (i + 1) hi'
      omega

theorem supportBound : Comparators.GorbowFreeSupport.SupportBound := ⟨termBound, formulaBound⟩

private theorem termUses (n : Nat) (t : Term n) (i : Fin n) :
    i.val ∈ termSupport t ↔ t.uses i = true := by
  induction t <;> simp_all [termSupport, Term.uses, Fin.ext_iff]

private theorem formulaUses (n : Nat) (φ : Formula n) :
    ∀ i : Fin n, i.val ∈ formulaSupport φ ↔ φ.uses i = true := by
  induction φ with
  | equal t u | knowledge t u => intro i; simp [formulaSupport, Formula.uses, termUses]
  | universalRelation t | agent t | knowledgeAll t | truth t => intro i; exact termUses _ t i
  | neg φ h => exact h
  | imp φ ψ hφ hψ | conj φ ψ hφ hψ | disj φ ψ hφ hψ =>
      intro i; simp [formulaSupport, Formula.uses, hφ, hψ]
  | all φ h | ex φ h =>
      intro i
      exact (unbindMembership (formulaSupport φ) i.val).trans (h i.succ)

theorem usesCalibration : Comparators.GorbowFreeSupport.UsesCalibration := ⟨termUses, formulaUses⟩

theorem exactContext : Comparators.GorbowFreeSupport.ExactContext := by
  intro n φ
  constructor
  · intro h i
    apply (formulaUses n φ i).mp
    change formulaSupport φ = Finset.range n at h
    rw [h]
    exact Finset.mem_range.mpr i.isLt
  · intro h
    apply Finset.ext
    intro i
    constructor
    · intro hi
      exact Finset.mem_range.mpr (formulaBound n φ i hi)
    · intro hi
      exact (formulaUses n φ ⟨i, Finset.mem_range.mp hi⟩).mpr (h _)

theorem preciseContext : Comparators.GorbowFreeSupport.PreciseContext := by
  intro n φ
  have hs : formulaSupport φ ⊆ Finset.range n := fun i hi => Finset.mem_range.mpr (formulaBound n φ i hi)
  constructor
  · intro h
    apply Finset.eq_of_subset_of_card_le hs
    simpa only [Finset.card_range] using (show n ≤ (formulaSupport φ).card from le_of_eq h.symm)
  · intro h
    change (formulaSupport φ).card = n
    rw [show formulaSupport φ = Finset.range n from h, Finset.card_range]

theorem selectorCalibration : Comparators.GorbowFreeSupport.SelectorCalibration := by
  have h (φ : Formula 1) : φ.uses 0 = true ↔ FreeNames {0} φ := by
    rw [show ({0} : Finset Nat) = Finset.range 1 by decide, exactContext]
    constructor
    · intro h i
      have hi : i = 0 := Fin.ext (by omega)
      simpa only [hi] using h
    · intro h
      exact h 0
  exact ⟨h, fun A => (h A.val).mp A.property⟩

private theorem termLocal (n : Nat) (t : Term n) (I : Interpretation) (v w : Fin n → Nat)
    (h : ∀ i : Fin n, i.val ∈ termSupport t → v i = w i) : t.realize I v = t.realize I w := by
  induction t with
  | var i => exact h i (by simp [termSupport])
  | zero => rfl
  | succ t ih => exact congrArg Nat.succ (ih h)
  | universalFunction t ih => exact congrArg I.universalFunction (ih h)
  | add t u ht hu | mul t u ht hu =>
      have ht' := ht (fun i hi => h i (Finset.mem_union_left _ hi))
      have hu' := hu (fun i hi => h i (Finset.mem_union_right _ hi))
      simp only [Term.realize, ht', hu']

private theorem formulaLocal (n : Nat) (φ : Formula n) (I : Interpretation) :
    ∀ (v w : Fin n → Nat), (∀ i : Fin n, i.val ∈ formulaSupport φ → v i = w i) →
    (φ.realize I v ↔ φ.realize I w) := by
  induction φ with
  | equal t u | knowledge t u =>
      intro v w h
      have ht := termLocal _ t I v w (fun i hi => h i (Finset.mem_union_left _ hi))
      have hu := termLocal _ u I v w (fun i hi => h i (Finset.mem_union_right _ hi))
      simp only [Formula.realize, ht, hu]
  | universalRelation t | agent t | knowledgeAll t | truth t =>
      intro v w h
      have ht := termLocal _ t I v w h
      simp only [Formula.realize, ht]
  | neg φ ih => intro v w h; exact not_congr (ih v w h)
  | imp φ ψ hφ hψ | conj φ ψ hφ hψ | disj φ ψ hφ hψ =>
      intro v w h
      have hp := hφ v w (fun i hi => h i (Finset.mem_union_left _ hi))
      have hq := hψ v w (fun i hi => h i (Finset.mem_union_right _ hi))
      simp only [Formula.realize, hp, hq]
  | all φ ih | ex φ ih =>
      intro v w h
      have he (x : Nat) : φ.realize I (Fin.cases x v) ↔ φ.realize I (Fin.cases x w) := by
        apply ih
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · intro _; rfl
        · intro hi
          apply h j
          exact (unbindMembership (formulaSupport φ) j.val).mpr hi
      first | exact forall_congr' he | exact exists_congr he

theorem semanticLocality : Comparators.GorbowFreeSupport.SemanticLocality := ⟨termLocal, formulaLocal⟩

theorem gorbowFreeSupport : Comparators.GorbowFreeSupport.Target :=
  ⟨unbindMembership, supportBound, usesCalibration, exactContext, preciseContext,
    selectorCalibration, semanticLocality⟩
end LogicLineages.ComputabilityKnowledge.GorbowFreeSupportProof
