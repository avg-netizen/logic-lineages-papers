module
public import LogicLineages.ModelsAlgebra.PGroups.BoundedTailScottTargets
public import LogicLineages.ModelsAlgebra.PGroups.LowerUlmDescriptorProof
public import LogicLineages.ModelsAlgebra.PGroups.PrimaryZeroSyntaxProof
public import LogicLineages.ModelsAlgebra.PGroups.ThreeRelativizationProof
public import LogicLineages.ModelsAlgebra.PGroups.BoundedTailCategoricityProof
public import LogicLineages.ModelsAlgebra.PGroups.BoundedScott
public import LogicLineages.ModelsAlgebra.PGroups.RawScott
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary

private theorem relative_sentence (G : Type) [AddCommGroup G] (S : AddSubgroup G) (φ : Formula 0) :
    φ.RealizeIn S (Fin.elim0 : Fin 0 → G) ↔ φ.Realize (Fin.elim0 : Fin 0 → S) := by
  have h := relativized_subgroup_agreement G S 0 φ (Fin.elim0 : Fin 0 → S)
  have he : (fun j : Fin 0 => ((Fin.elim0 j : S):G)) = Fin.elim0 := by
    funext j; exact Fin.elim0 j
  simpa only [he] using h

theorem bounded_tail_scott_upper : Targets.boundedTailScottUpper := by
  classical
  intro p _ G _ _ γ _ N hprimary hN
  let S : AddSubgroup G := transfiniteFiltration p (Ordinal.omega0*γ)
  obtain ⟨entries,htail,hscott⟩ := bounded_pi_three_scott p S N hN
  obtain ⟨tail,ht,htsem⟩ := three_transfinite_relativization.{0} p γ .pi 0
    (boundedUlmTable p N entries) htail
  obtain ⟨lo,hlo,hlosem⟩ := lower_ulm_descriptor p G γ
  have hlbound : 2*γ+1 ≤ 2*γ+3 := by
    simpa only [add_assoc,show (1:Ordinal)+2=3 from by norm_num] using
      (le_self_add : 2*γ+1 ≤ (2*γ+1)+2)
  have hthree : (3:Ordinal) ≤ 2*γ+3 := le_add_self
  have htwo : (2:Ordinal) ≤ 2*γ+3 := (by rw [show (3:Ordinal)=2+1 from by norm_num]; exact le_self_add : (2:Ordinal) ≤ 3).trans hthree
  have hl := positive_complexity_monotone .pi (2*γ+1) (2*γ+3) 0 lo (by positivity) hlbound hlo
  have hp := positive_complexity_monotone .pi 2 (2*γ+3) 0 (primarySentence p)
    two_ne_zero htwo (primary_sentence_exact.{0} p).1
  let fs : List (Formula 0) := [lo,tail,primarySentence p]
  have hf : ∀ φ ∈ fs, Complexity .pi (2*γ+3) φ := by
    intro φ hφ
    simp only [fs,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hφ
    rcases hφ with rfl | rfl | rfl
    · exact hl
    · exact ht
    · exact hp
  obtain ⟨hc,hsem⟩ := pi_finite_guard_exact.{0} (2*γ+3) 0 fs hf
  let φ := piFiniteGuard (2*γ+3) fs
  have hs : GroupScottSentence G φ := by
    constructor
    · apply (hsem G Fin.elim0).mpr
      intro ψ hψ
      simp only [fs,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hψ
      rcases hψ with rfl | rfl | rfl
      · exact (hlosem G).mpr (fun _ _ => rfl)
      · exact (htsem G Fin.elim0).mpr ((relative_sentence G S _).mpr hscott.1)
      · exact (primary_sentence_exact.{0} p).2 G |>.mpr hprimary
    · intro H _ _ hφ
      let T : AddSubgroup H := transfiniteFiltration p (Ordinal.omega0*γ)
      have hh := (hsem H Fin.elim0).mp hφ
      have hlower := (hlosem H).mp (hh lo (by simp [fs]))
      have hprimaryH := (primary_sentence_exact.{0} p).2 H |>.mp (hh (primarySentence p) (by simp [fs]))
      have htailH := (relative_sentence H T _).mp ((htsem H Fin.elim0).mp (hh tail (by simp [fs])))
      obtain ⟨e⟩ := hscott.2 T htailH
      exact bounded_tail_categoricity G H p hprimary hprimaryH (Ordinal.omega0*γ) N hN e hlower
  exact ⟨guardPi φ,raw_guard_pi_complexity _ ((by norm_num : (1:Ordinal) ≤ 3).trans hthree) φ hc,
    raw_guard_scott_transfer G φ hs⟩
end LogicLineages.ModelsAlgebra.PGroups
