module
public import LogicLineages.ModelsAlgebra.PGroups.ShortSigmaCollapseTargets
public import LogicLineages.ModelsAlgebra.PGroups.CloseAllProof
public import LogicLineages.ModelsAlgebra.PGroups.TupleOrbitProof
public import LogicLineages.ModelsAlgebra.PGroups.RawScott
public import LogicLineages.ModelsAlgebra.PGroups.RawScottRestriction
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary GroupBackAndForth

private theorem twice_bound (γ:Ordinal.{0}) (hγ:0<γ) : 2≤2*γ := by
  have h := mul_le_mul_left' (Order.one_le_iff_ne_zero.mpr (ne_of_gt hγ)) (2:Ordinal.{0})
  simpa only [mul_one] using h

theorem short_stable_sigma_scott_lowering : Targets.shortStableSigmaScottLowering := by
  classical
  intro p _ G _ _ γ _ α hγ hα hG hαγ hstable φ hφ hScott
  have htwo := twice_bound γ hγ
  have hlevel : (2*γ:Ordinal.{0})≠0 := by
    intro hz
    rw [hz] at htwo
    exact not_le_of_gt (show (0:Ordinal.{0})<2 from zero_lt_two) htwo
  generalize he : 2*γ+1=η at hφ
  cases hφ with
  | qf side q => exact ((by simp : (2*γ+1:Ordinal.{0})≠0) he).elim
  | sigma hpos s m matrix β lower rank =>
    subst η
    obtain ⟨i,c,hc⟩ := hScott.1
    let n := 0+m i
    let a : Fin n→G := append Fin.elim0 c
    have hβ : β i≤2*γ := Order.le_of_lt_succ
      (by simpa only [Order.succ_eq_add_one] using lower i)
    let Φ := piOneNormalize (matrix i)
    have hΦ : Complexity .pi (2*γ) Φ :=
      (raw_pi_normalization (β i) (2*γ) hlevel hβ n (matrix i) (rank i)).1
    have hΦa : Φ.Realize a := (pi_one_normalization_realization G n (matrix i) a).mpr hc
    obtain ⟨ψ,hψ,hψsem⟩ := short_stable_tuple_orbit_definable p G γ α hγ hα
      hG hαγ hstable n a
    let imp := (sigmaTwoConjunction ψ Φ.dual).dual
    have hImp : Complexity .pi (2*γ) imp :=
      dual_complexity .sigma (2*γ) n (sigmaTwoConjunction ψ Φ.dual)
        (higher_sigma_conjunction_complexity (2*γ) htwo n ψ Φ.dual hψ
          (dual_complexity .pi (2*γ) n Φ hΦ))
    have hlogic : ∀ (H:Type) [AddCommGroup H] (b:Fin n→H),
        imp.Realize b ↔ (ψ.Realize b → Φ.Realize b) := by
      intro H _ b
      change (sigmaTwoConjunction ψ Φ.dual).dual.Realize b ↔ _
      rw [dual_realization H n (sigmaTwoConjunction ψ Φ.dual) b,
        sigma_two_conjunction_realization H n ψ Φ.dual b,dual_realization H n Φ b]
      constructor
      · intro h hy
        by_contra hn
        exact h ⟨hy,hn⟩
      · intro h hc
        exact hc.2 (h hc.1)
    obtain ⟨hEx,hExsem⟩ := sigma_close_all_correct (2*γ) hlevel n ψ hψ
    obtain ⟨hAll,hAllsem⟩ := pi_close_all_correct (2*γ) hlevel n imp hImp
    let d : DifferenceFormula 0 := ⟨sigmaCloseAll ψ,piCloseAll imp⟩
    refine ⟨d,⟨hEx,hAll⟩,⟨?_,?_⟩,?_⟩
    · apply (hExsem G).mpr
      exact ⟨a,(hψsem a).mpr ⟨AddEquiv.refl G,fun _=>rfl⟩⟩
    · apply (hAllsem G).mpr
      intro b
      apply (hlogic G b).mpr
      intro hψb
      obtain ⟨u,hu⟩ := (hψsem b).mp hψb
      have hbf := comparison_isomorphism (2*γ) G G u n a
      rw [funext hu] at hbf
      exact (truth_transfer (2*γ) G G n a b hbf).1 Φ hΦ hΦa
    · intro H _ _ hd
      obtain ⟨b,hb⟩ := (hExsem H).mp hd.1
      have hi := (hAllsem H).mp hd.2 b
      have hm : (matrix i).Realize b :=
        (pi_one_normalization_realization H n (matrix i) b).mp ((hlogic H b).mp hi hb)
      let cH : Fin (m i)→H := fun j=>b (Fin.natAdd 0 j)
      have happend : append (Fin.elim0:Fin 0→H) cH=b := by
        funext j
        induction j using Fin.addCases with
        | left j => exact j.elim0
        | right j =>
          exact Fin.addCases_right (m:=0) (n:=m i) (motive:=fun _=>H)
            (left:=(Fin.elim0:Fin 0→H)) (right:=cH) j
      apply hScott.2 H
      refine ⟨i,cH,?_⟩
      rw [happend]
      exact hm

theorem short_stable_raw_sigma_scott_lowering : Targets.shortStableRawSigmaScottLowering := by
  intro p _ G _ _ γ _ α hγ hα hG hαγ hstable φ hφ hScott
  obtain ⟨d,hd,hS⟩ := short_stable_sigma_scott_lowering p G γ α hγ hα hG hαγ hstable
    φ hφ (raw_scott_restriction G φ hScott)
  refine ⟨guardDifference d,raw_guard_difference_complexity (2*γ)
    ((show (1:Ordinal.{0})≤2 from one_le_two).trans (twice_bound γ hγ)) d hd,
    raw_guard_difference_scott_transfer G d hS⟩

end LogicLineages.ModelsAlgebra.PGroups
