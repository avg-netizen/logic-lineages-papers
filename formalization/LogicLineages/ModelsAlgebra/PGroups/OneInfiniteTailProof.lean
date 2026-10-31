module
public import LogicLineages.ModelsAlgebra.PGroups.OneInfiniteTailTargets
public import LogicLineages.ModelsAlgebra.PGroups.LowerUlmDescriptorProof
public import LogicLineages.ModelsAlgebra.PGroups.PrimaryZeroSyntaxProof
public import LogicLineages.ModelsAlgebra.PGroups.BoundedTailCategoricityProof
public import LogicLineages.ModelsAlgebra.PGroups.IntrinsicBoundedScott
public import LogicLineages.ModelsAlgebra.PGroups.FiniteTail
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

private theorem lift_pi_two (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G]
    (γ : Ordinal.{0}) [Countable γ.ToType] (N : ℕ)
    (hprimary : ∀ x : G, ∃ k : ℕ, p^k • x=0)
    (hN : ∀ x : (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G), p^N • x=0)
    (input : Formula 0) (htail : Complexity .pi (2:Ordinal.{0}) input)
    (hscott : GroupScottSentence (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) input) :
    ∃ φ : Formula 0, Complexity .pi (2*γ+2) φ ∧ RawScottSentence (RawGroupStructure.ofGroup G) φ := by
  classical
  let S : AddSubgroup G := transfiniteFiltration p (Ordinal.omega0*γ)
  obtain ⟨tail,ht,htsem⟩ := low_transfinite_relativization.{0} p γ .pi 2 (Or.inr rfl) 0 input htail
  obtain ⟨lo,hlo,hlosem⟩ := lower_ulm_descriptor p G γ
  have hlbound : 2*γ+1 ≤ 2*γ+2 := by
    simpa only [Order.succ_eq_add_one,add_assoc,one_add_one_eq_two] using (Order.le_succ (2*γ+1))
  have htwo : (2:Ordinal) ≤ 2*γ+2 := le_add_self
  have hl := positive_complexity_monotone .pi (2*γ+1) (2*γ+2) 0 lo (by positivity) hlbound hlo
  have hp := positive_complexity_monotone .pi 2 (2*γ+2) 0 (primarySentence p)
    two_ne_zero htwo (primary_sentence_exact.{0} p).1
  let fs : List (Formula 0) := [lo,tail,primarySentence p]
  have hf : ∀ φ ∈ fs, Complexity .pi (2*γ+2) φ := by
    intro φ hφ
    simp only [fs,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hφ
    rcases hφ with rfl | rfl | rfl
    · exact hl
    · exact ht
    · exact hp
  obtain ⟨hc,hsem⟩ := pi_finite_guard_exact.{0} (2*γ+2) 0 fs hf
  let φ := piFiniteGuard (2*γ+2) fs
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
  exact ⟨guardPi φ,raw_guard_pi_complexity _ (one_le_two.trans htwo) φ hc,
    raw_guard_scott_transfer G φ hs⟩

private theorem lift_difference_two (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G]
    (γ : Ordinal.{0}) [Countable γ.ToType] (N : ℕ)
    (hprimary : ∀ x : G, ∃ k : ℕ, p^k • x=0)
    (hN : ∀ x : (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G), p^N • x=0)
    (d : DifferenceFormula 0) (hd : d.AtLevel (2:Ordinal.{0}))
    (hscott : DifferenceScottSentence (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) d) :
    ∃ out : DifferenceFormula 0, out.AtLevel (2*γ+2) ∧ RawDifferenceScottSentence (RawGroupStructure.ofGroup G) out := by
  classical
  let S : AddSubgroup G := transfiniteFiltration p (Ordinal.omega0*γ)
  obtain ⟨sig,hsig,hsigsem⟩ := low_transfinite_relativization.{0} p γ .sigma 2 (Or.inr rfl) 0 d.sigmaPart hd.1
  obtain ⟨pi,hpi,hpisem⟩ := low_transfinite_relativization.{0} p γ .pi 2 (Or.inr rfl) 0 d.piPart hd.2
  obtain ⟨lo,hlo,hlosem⟩ := lower_ulm_descriptor p G γ
  have hlbound : 2*γ+1 ≤ 2*γ+2 := by
    simpa only [Order.succ_eq_add_one,add_assoc,one_add_one_eq_two] using (Order.le_succ (2*γ+1))
  have hlo' := positive_complexity_monotone .pi (2*γ+1) (2*γ+2) 0 lo (by positivity) hlbound hlo
  have htwo : (2:Ordinal) ≤ 2*γ+2 := le_add_self
  have hp := positive_complexity_monotone .pi 2 (2*γ+2) 0 (primarySentence p)
    two_ne_zero htwo (primary_sentence_exact.{0} p).1
  let fs : List (Formula 0) := [pi,lo,primarySentence p]
  have hf : ∀ φ ∈ fs, Complexity .pi (2*γ+2) φ := by
    intro φ hφ
    simp only [fs,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hφ
    rcases hφ with rfl | rfl | rfl
    · exact hpi
    · exact hlo'
    · exact hp
  obtain ⟨hc,hsem⟩ := pi_finite_guard_exact.{0} (2*γ+2) 0 fs hf
  let out : DifferenceFormula 0 := ⟨sig,piFiniteGuard (2*γ+2) fs⟩
  have hout : DifferenceScottSentence G out := by
    constructor
    · refine ⟨(hsigsem G Fin.elim0).mpr ((relative_sentence G S _).mpr hscott.1.1),?_⟩
      apply (hsem G Fin.elim0).mpr
      intro ψ hψ
      simp only [fs,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hψ
      rcases hψ with rfl | rfl | rfl
      · exact (hpisem G Fin.elim0).mpr ((relative_sentence G S _).mpr hscott.1.2)
      · exact (hlosem G).mpr (fun _ _ => rfl)
      · exact (primary_sentence_exact.{0} p).2 G |>.mpr hprimary
    · intro H _ _ hH
      let T : AddSubgroup H := transfiniteFiltration p (Ordinal.omega0*γ)
      have hh := (hsem H Fin.elim0).mp hH.2
      have htS := (relative_sentence H T _).mp ((hsigsem H Fin.elim0).mp hH.1)
      have htP := (relative_sentence H T _).mp ((hpisem H Fin.elim0).mp (hh pi (by simp [fs])))
      obtain ⟨e⟩ := hscott.2 T ⟨htS,htP⟩
      exact bounded_tail_categoricity G H p hprimary
        ((primary_sentence_exact.{0} p).2 H |>.mp (hh (primarySentence p) (by simp [fs])))
        (Ordinal.omega0*γ) N hN e ((hlosem H).mp (hh lo (by simp [fs])))
  exact ⟨guardDifference out,raw_guard_difference_complexity _ (one_le_two.trans htwo) out ⟨hsig,hc⟩,
    raw_guard_difference_scott_transfer G out hout⟩

private theorem source_images (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G]
    (k N : ℕ) (hk : 0 < k) (hkN : k ≤ N) (hb : ∀ g : G, p^N • g=0)
    (hm : Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (k-1) : AddSubgroup G)) = Cardinal.aleph0)
    (ho : ∀ j : ℕ, j<N → j≠k-1 → Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) < Cardinal.aleph0) :
    Finite (multipleImage G (p^k)) ∧ Infinite (multipleImage G (p^(k-1))) := by
  have hf := finite_tail_from_ranks p G N hb k hkN (fun j hkj hjN => ho j hjN (by omega))
  have hi := infinite_ulm_infinite_filtration p G (k-1) hm
  rw [finite_filtration_multiple_image G p k] at hf
  rw [finite_filtration_multiple_image G p (k-1)] at hi
  exact ⟨hf,hi⟩

theorem one_infinite_tail_pi_upper : Targets.oneInfiniteTailPiUpper := by
  intro p _ G _ _ γ _ k N hprimary hk hkN hN hm ho hz
  let S : AddSubgroup G := transfiniteFiltration p (Ordinal.omega0*γ)
  obtain ⟨hf,hi⟩ := source_images p S k N hk hkN hN hm ho
  obtain ⟨φ,hφ,hscott⟩ := intrinsic_bounded_pi_scott p S k N hk hkN hN hf hi hz
  exact lift_pi_two p G γ N hprimary hN φ hφ hscott

theorem one_infinite_tail_difference_upper : Targets.oneInfiniteTailDifferenceUpper := by
  intro p _ G _ _ γ _ k N hprimary hk hkN hN hm ho
  let S : AddSubgroup G := transfiniteFiltration p (Ordinal.omega0*γ)
  obtain ⟨hf,hi⟩ := source_images p S k N hk hkN hN hm ho
  obtain ⟨d,hd,hscott⟩ := intrinsic_bounded_difference_scott p S k N hk hkN hN hf hi
    (fun j hj => ho j (by omega) (by omega))
  exact lift_difference_two p G γ N hprimary hN d hd hscott
end LogicLineages.ModelsAlgebra.PGroups
