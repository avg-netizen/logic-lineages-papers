module
public import LogicLineages.ModelsAlgebra.PGroups.LimitSigmaScottTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary

theorem raw_limit_sigma_scott_lowering : Targets.rawLimitSigmaScottLowering := by
  intro G _ R α _ hlimit φ hc hs
  cases hc with
  | qf side q => exact (hlimit.ne_zero rfl).elim
  | sigma hpos s m matrix β lower rank =>
    obtain ⟨i,c,hc⟩ := hs.1
    let ψ : Formula 0 := .disjEx {0} (fun _=>m i) (fun _=>matrix i)
    refine ⟨β i+1,?_,ψ,?_,?_,?_⟩
    · simpa only [Order.succ_eq_add_one] using hlimit.succ_lt (lower i)
    · exact Complexity.sigma (α:=β i+1)
        (ne_of_gt (lt_of_le_of_lt zero_le (by simpa only [Order.succ_eq_add_one] using
          (Order.lt_succ (β i))))) {0} (fun _=>m i) (fun _=>matrix i)
        (fun _=>β i) (fun _=>by simpa only [Order.succ_eq_add_one] using Order.lt_succ (β i))
        (fun _=>rank i)
    · exact ⟨⟨0,by simp⟩,c,hc⟩
    · intro H _ S ht
      obtain ⟨_,d,hd⟩ := ht
      exact hs.2 H S ⟨i,d,hd⟩

end LogicLineages.ModelsAlgebra.PGroups
