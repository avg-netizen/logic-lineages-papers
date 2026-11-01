module
public import LogicLineages.OrdinalComparison.HeadGraphShiftTargets
public import LogicLineages.OrdinalComparison.HeadWindowNextProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.HeadGraphShift

theorem actual_shift : Targets.ActualFiniteOmegaHeadShift := by
  intro beta hbeta hlimit delta
  dsimp only
  induction delta with
  | zero =>
    simp only [Nat.cast_zero,mul_zero,add_zero,Function.iterate_zero,id_eq]
    exact ⟨hbeta,hlimit,True.intro,fun t ht => ⟨ht,True.intro,True.intro,True.intro⟩⟩
  | succ delta ih =>
    rcases ih with ⟨he,hl,hn,hr⟩
    have hstep := actualNextLimitHeadFacts
      (beta + Ordinal.omega0 * (delta : Ordinal)) he hl
    have hsucc : beta + Ordinal.omega0 * ((delta+1 : Nat) : Ordinal) =
        (beta + Ordinal.omega0 * (delta : Ordinal)) + Ordinal.omega0 := by
      simp only [Nat.cast_add,Nat.cast_one,mul_add_one,add_assoc]
    have hn' : actualOrdinalNorm (beta + Ordinal.omega0 * ((delta+1 : Nat) : Ordinal)) =
        actualOrdinalNorm beta + 2*(delta+1) := by
      rw [hsucc,hstep.2.2.1,hn]
      omega
    refine ⟨?_,?_,hn',?_⟩
    · rw [hsucc]
      exact hstep.1
    · rw [hsucc]
      exact hstep.2.1
    · intro t ht
      have hdom : actualOrdinalNorm (beta + Ordinal.omega0 * (delta : Ordinal))+2 ≤ t := by
        rw [hn'] at ht
        rw [hn]
        omega
      have hf : actualOrdinalNorm (beta + Ordinal.omega0 * (delta : Ordinal)) ≤ Phi t :=
        (by omega : actualOrdinalNorm (beta + Ordinal.omega0 * (delta : Ordinal)) ≤ t).trans
          (self_lt_Phi t).le
      have hs := hstep.2.2.2 t hdom
      have hi := hr (Phi t) hf
      refine ⟨?_,?_,?_,?_⟩
      · simpa only [Function.iterate_succ_apply] using hi.1
      · rw [hsucc,hs.2.1,hi.2.1,Function.iterate_succ_apply]
      · rw [hsucc,hs.2.2.1,hi.2.2.1,Function.iterate_succ_apply]
        omega
      · rw [hsucc,hs.2.2.2,hi.2.2.2,Function.iterate_succ_apply]
        omega

end LogicLineages.OrdinalComparison.HeadGraphShift
