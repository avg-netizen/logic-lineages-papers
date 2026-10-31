module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteTailScottTargets
public import LogicLineages.ModelsAlgebra.PGroups.LowerUlmDescriptorProof
public import LogicLineages.ModelsAlgebra.PGroups.PrimaryZeroSyntaxProof
public import LogicLineages.ModelsAlgebra.PGroups.BoundedTailCategoricityProof
public import LogicLineages.ModelsAlgebra.PGroups.FiniteScott
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

private theorem finite_primary_bound (G : Type) [AddCommGroup G] [Finite G] (p : ℕ)
    (hp : ∀ x : G, ∃ k : ℕ, p^k • x=0) : ∃ N : ℕ, ∀ x : G, p^N • x=0 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  choose k hk using hp
  refine ⟨Finset.univ.sup k,?_⟩
  intro x
  have hle : k x ≤ Finset.univ.sup k := Finset.le_sup (Finset.mem_univ x)
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le hle
  rw [hj,pow_add,mul_nsmul,hk,nsmul_zero]

theorem finite_tail_scott_upper : Targets.finiteTailScottUpper := by
  classical
  intro p _ G _ _ γ _ hprimary hfinite
  by_cases hγ : γ=0
  · subst γ
    have ht : Finite (⊤ : AddSubgroup G) := by
      simpa only [mul_zero,transfiniteFiltration_zero] using hfinite
    letI := ht
    letI : Finite G := Finite.of_surjective (⊤ : AddSubgroup G).subtype (fun x => ⟨⟨x,trivial⟩,rfl⟩)
    letI : Fintype G := Fintype.ofFinite G
    refine ⟨guardDifference (finiteImageIsomorphismFormula G 1),?_,
      raw_guard_difference_scott_transfer G _ (finite_difference_scott G)⟩
    simpa only [mul_zero,zero_add] using
      raw_guard_difference_complexity 1 le_rfl _ (finite_isomorphism_sentence.{0,0,0} G).1
  · let S : AddSubgroup G := transfiniteFiltration p (Ordinal.omega0*γ)
    letI : Finite S := hfinite
    letI : Fintype S := Fintype.ofFinite S
    have hS : ∀ x : S, ∃ k : ℕ, p^k • x=0 := by
      intro x
      obtain ⟨k,hk⟩ := hprimary x
      exact ⟨k,Subtype.ext hk⟩
    obtain ⟨N,hN⟩ := finite_primary_bound S p hS
    let d := finiteImageIsomorphismFormula S 1
    have hd := (finite_isomorphism_sentence.{0,0,0} S).1
    have hscott := finite_difference_scott S
    obtain ⟨sig,hsig,hsigsem⟩ := low_transfinite_relativization.{0} p γ .sigma 1 (Or.inl rfl) 0 d.sigmaPart (by simpa only [Nat.cast_one] using hd.1)
    obtain ⟨pi,hpi,hpisem⟩ := low_transfinite_relativization.{0} p γ .pi 1 (Or.inl rfl) 0 d.piPart (by simpa only [Nat.cast_one] using hd.2)
    simp only [Nat.cast_one] at hsig hpi
    obtain ⟨lo,hlo,hlosem⟩ := lower_ulm_descriptor p G γ
    have htwo : (2:Ordinal) ≤ 2*γ+1 := calc
      2 = 2*1 := by simp
      _ ≤ 2*γ := mul_le_mul_left' (Order.one_le_iff_ne_zero.mpr hγ) 2
      _ ≤ 2*γ+1 := le_self_add
    have hp := positive_complexity_monotone .pi 2 (2*γ+1) 0 (primarySentence p)
      two_ne_zero htwo (primary_sentence_exact.{0} p).1
    let fs : List (Formula 0) := [pi,lo,primarySentence p]
    have hf : ∀ φ ∈ fs, Complexity .pi (2*γ+1) φ := by
      intro φ hφ
      simp only [fs,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hφ
      rcases hφ with rfl | rfl | rfl
      · exact hpi
      · exact hlo
      · exact hp
    obtain ⟨hc,hsem⟩ := pi_finite_guard_exact.{0} (2*γ+1) 0 fs hf
    let out : DifferenceFormula 0 := ⟨sig,piFiniteGuard (2*γ+1) fs⟩
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
end LogicLineages.ModelsAlgebra.PGroups
