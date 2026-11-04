module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ReverseWindowTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ReverseWindowProof
open ReverseWindow

theorem actualMinusWitness : ReverseWindowTargets.ActualMinusWitness := by
  intro i anchor e c ν hp
  have hdom : 0 ≤ (ν i : Int) + e := by
    have hi : (-e).toNat ≤ ν i := Nat.le_of_not_gt hp.1
    omega
  have hlo : Phi ((shiftTerm (.variable i) e).value ν) ≤ Phi (anchor.value ν) :=
    Nat.le_of_not_gt hp.2.1
  have hhi : Phi (anchor.value ν) ≤ c * Phi ((shiftTerm (.variable i) e).value ν) :=
    Nat.le_of_not_gt hp.2.2
  obtain ⟨d, hd, heq⟩ := WindowProof.actualArgumentWindow
    (anchor.value ν) ((shiftTerm (.variable i) e).value ν) c hlo hhi
  refine ⟨d, hd, heq, ?_⟩
  have hsub : anchor.value ν - d = (shiftTerm (.variable i) e).value ν := by omega
  rw [ReverseWindow.replacementTerm, WindowProof.shifted_value]
  simp only [Term.value]
  rw [hsub, WindowProof.shifted_value]
  simp only [Term.value]
  omega

private theorem finite_truth (i : Nat) (anchor : Term) (e : Int) (c : Nat) (p : Matrix)
    (ν : Nat → Nat) :
    (ReverseWindow.finiteCases i anchor e c p).eval ν ↔
      ∃ d : Nat, d ≤ c ∧
        (Matrix.conjunction (ReverseWindow.closeMatrix i anchor e c) p).eval
          (Function.update ν i ((ReverseWindow.replacementTerm anchor e d).value ν)) := by
  rw [ReverseWindow.finiteCases, WindowProof.any_truth]
  constructor
  · rintro ⟨q, hq, hp⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
    exact ⟨d, by have := List.mem_range.mp hd; omega,
      (WindowProof.matrix_substitution _ _ _ _).mp hp⟩
  · rintro ⟨d, hd, hp⟩
    exact ⟨_, List.mem_map.mpr ⟨d, List.mem_range.mpr (by omega), rfl⟩,
      (WindowProof.matrix_substitution _ _ _ _).mpr hp⟩

private theorem replacement_support (anchor : Term) (e : Int) (d : Nat) :
    (ReverseWindow.replacementTerm anchor e d).variables = anchor.variables := by
  simp [ReverseWindow.replacementTerm, shiftTerm, Term.variables]

theorem actualFiniteElimination : ReverseWindowTargets.ActualFiniteElimination := by
  intro i anchor e c p hi ν
  constructor
  · rintro ⟨n, hc, hp⟩
    obtain ⟨d, hd, heq, hr⟩ := actualMinusWitness i anchor e c (Function.update ν i n) hc
    have hir : i ∉ (ReverseWindow.replacementTerm anchor e d).variables := by
      simpa only [replacement_support] using hi
    rw [WindowProof.term_update _ i n ν hir, Function.update_self] at hr
    apply (finite_truth i anchor e c p ν).mpr
    refine ⟨d, hd, ?_⟩
    rw [hr]
    exact ⟨hc, hp⟩
  · intro hp
    obtain ⟨d, hd, hp⟩ := (finite_truth i anchor e c p ν).mp hp
    exact ⟨_, hp.1, hp.2⟩

theorem exactSupportReduction : ReverseWindowTargets.ExactSupportReduction := by
  intro i anchor e c p hi v hv
  rw [ReverseWindow.finiteCases, WindowProof.any_support] at hv
  obtain ⟨q, hq, hv⟩ := hv
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
  have hs := (WindowProof.matrix_support
    (Matrix.conjunction (ReverseWindow.closeMatrix i anchor e c) p)
    (ReverseWindow.replacementTerm anchor e d) i v).mp hv
  have hc : v ∈ (ReverseWindow.closeMatrix i anchor e c).variables →
      v = i ∨ v ∈ anchor.variables := by
    simp only [ReverseWindow.closeMatrix, shiftDomain, atMost, shiftTerm,
      Matrix.variables, Term.variables, List.mem_append, List.mem_singleton, List.not_mem_nil]
    tauto
  rcases hs with ⟨hs, hne⟩ | ⟨_, hr⟩
  · rcases List.mem_append.mp hs with hclose | hp
    · rcases hc hclose with he | ha
      · exact False.elim (hne he)
      · exact ⟨hne, Or.inl ha⟩
    · exact ⟨hne, Or.inr hp⟩
  · have ha : v ∈ anchor.variables := by simpa only [replacement_support] using hr
    exact ⟨by intro he; subst v; exact hi ha, Or.inl ha⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ReverseWindowProof
