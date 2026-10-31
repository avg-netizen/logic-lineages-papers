module
public import LogicLineages.ModelsAlgebra.PGroups.ZeroCutScottTargets
public import LogicLineages.ModelsAlgebra.PGroups.LowerUlmDescriptorProof
public import LogicLineages.ModelsAlgebra.PGroups.PrimaryZeroSyntaxProof
public import LogicLineages.ModelsAlgebra.PGroups.CountableUlmProof
public import LogicLineages.ModelsAlgebra.PGroups.RawScott
public import LogicLineages.ModelsAlgebra.PGroups.TrivialScott
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary

theorem zero_cut_scott_upper : Targets.zeroCutScottUpper := by
  classical
  intro p _ G _ _ γ _ hprimary hzero
  by_cases hγ : γ=0
  · subst γ
    have hz : (⊤ : AddSubgroup G)=⊥ := by simpa only [mul_zero,transfiniteFiltration_zero] using hzero
    letI : Subsingleton G := ⟨fun x y => (hz.le (show x ∈ (⊤ : AddSubgroup G) from trivial)).trans
      (hz.le (show y ∈ (⊤ : AddSubgroup G) from trivial)).symm⟩
    refine ⟨guardPi (annihilationFormula 1 0),?_,raw_guard_scott_transfer G _ (trivial_pi_one_scott.{0,0}.2 G)⟩
    simpa only [mul_zero,zero_add] using
      raw_guard_pi_complexity 1 le_rfl _ trivial_pi_one_scott.{0,0}.1
  · have hγ1 : 1 ≤ γ := Order.one_le_iff_ne_zero.mpr hγ
    have htwo : (2:Ordinal) ≤ 2*γ+1 := calc
      2 = 2*1 := by simp
      _ ≤ 2*γ := mul_le_mul_left' hγ1 2
      _ ≤ 2*γ+1 := le_self_add
    obtain ⟨lo,hlo,hlosem⟩ := lower_ulm_descriptor p G γ
    obtain ⟨zero,hz,hzsem⟩ := zero_stage_descriptor.{0} p γ 0
    have hp := positive_complexity_monotone .pi 2 (2*γ+1) 0 (primarySentence p)
      two_ne_zero htwo (primary_sentence_exact.{0} p).1
    let fs : List (Formula 0) := [lo,zero,primarySentence p]
    have hf : ∀ φ ∈ fs, Complexity .pi (2*γ+1) φ := by
      intro φ hφ
      simp only [fs,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hφ
      rcases hφ with rfl | rfl | rfl
      · exact hlo
      · exact hz
      · exact hp
    obtain ⟨hc,hsem⟩ := pi_finite_guard_exact.{0} (2*γ+1) 0 fs hf
    let φ := piFiniteGuard (2*γ+1) fs
    have hs : GroupScottSentence G φ := by
      constructor
      · apply (hsem G Fin.elim0).mpr
        intro ψ hψ
        simp only [fs,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hψ
        rcases hψ with rfl | rfl | rfl
        · exact (hlosem G).mpr (fun _ _ => rfl)
        · exact (hzsem G).mpr (by simpa only [Nat.cast_zero,add_zero] using hzero)
        · exact (primary_sentence_exact.{0} p).2 G |>.mpr hprimary
      · intro H _ _ ht
        have ht' := (hsem H Fin.elim0).mp ht
        have hl := (hlosem H).mp (ht' lo (by simp [fs]))
        have hh := (primary_sentence_exact.{0} p).2 H |>.mp (ht' (primarySentence p) (by simp [fs]))
        have hzH := (hzsem H).mp (ht' zero (by simp [fs]))
        simp only [Nat.cast_zero,add_zero] at hzH
        exact countable_ulm_at_zero_cut G H p hprimary hh (Ordinal.omega0*γ)
          (Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 (lt_of_le_of_ne zero_le (Ne.symm hγ)))
          hzero hzH hl
    exact ⟨guardPi φ,raw_guard_pi_complexity _ (one_le_two.trans htwo) φ hc,
      raw_guard_scott_transfer G φ hs⟩
end LogicLineages.ModelsAlgebra.PGroups
