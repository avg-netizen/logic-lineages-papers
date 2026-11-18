module
public import LogicLineages.PermittedControl.GapReserveProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem gapInputComparison : Targets.GapInputComparison := by
  intro f B hf lam mu lam' mu' ha ha' hl hl' hmu hmu' hml hml'
  let S := gapProfileBound mu mu'
  have hS : actualOrdinalNorm mu ≤ S ∧ actualOrdinalNorm mu' ≤ S ∧ 1 ≤ S := by
    dsimp [S, gapProfileBound]
    omega
  have had := selected_threshold_admissible f B hf
  have hstep : ∀ n, n ≤ f n := control_self_le f had.2
  refine ⟨?_, ?_, ?_⟩
  · intro hgap t ht
    have htails := gap_tail_bounds lam mu lam' mu' 0
    have htP := htails.1.trans ht
    have htQ := htails.2.1.trans ht
    have hSt : S ≤ t := htails.2.2.1.trans ht
    obtain ⟨i,hi,hEi⟩ := entryExistenceOrbit f B hf lam mu t ha hl hmu hml htP
    obtain ⟨j,hj,hEj⟩ := entryExistenceOrbit f B hf lam' mu' t ha' hl' hmu' hml' htQ
    have hc := countLag f f B B hf hf lam' mu' lam mu t t j i 0 S ha' ha hl' hl hmu' hmu
      hml' hml htQ htP hS.2.1 hS.1 hj hi
    have hcount : j < i := by
      have hr := hc.1 (by
        rw [gap_initial_limit f lam' mu' t hl' hml', gap_initial_limit f lam mu t hl hml]
        exact hgap) (by
          intro a _
          have hSa : S ≤ f^[a] t := hSt.trans (iterate_self_le hstep a t)
          simpa only [Nat.add_zero, Function.iterate_succ_apply'] using selected_margin f B hf S (f^[a] t) hSa)
      simpa using hr
    refine ⟨i,j,hi,hj,hcount,?_⟩
    rw [hEj,hEi]
    exact selected_iterate_strict f B hf t hcount
  · intro hgap t u ht hu hut
    have htails := gap_tail_bounds lam mu lam' mu' 0
    have htP := htails.1.trans ht
    have huQ := htails.2.1.trans hu
    have hSu : S ≤ u := htails.2.2.1.trans hu
    obtain ⟨i,hi,hEi⟩ := entryExistenceOrbit f B hf lam mu t ha hl hmu hml htP
    obtain ⟨j,hj,hEj⟩ := entryExistenceOrbit f B hf lam' mu' u ha' hl' hmu' hml' huQ
    have hc := countLag f f B B hf hf lam' mu' lam mu u t j i 0 S ha' ha hl' hl hmu' hmu
      hml' hml huQ htP hS.2.1 hS.1 hj hi
    have hcount : j ≤ i := by
      have hr := hc.2 (by
        rw [gap_initial_limit f lam' mu' u hl' hml', gap_initial_limit f lam mu t hl hml]
        exact hgap) (by
          intro a _
          have hSa := hSu.trans (iterate_self_le hstep a u)
          have hlt := had.1.iterate a hut
          simpa only [Nat.add_zero, Function.iterate_succ_apply'] using
            selected_input_margin f B hf S (f^[a] u) (f^[a] t) hSa hlt)
      simpa using hr
    refine ⟨i,j,hi,hj,hcount,?_⟩
    rw [hEj,hEi]
    exact (had.1.iterate j hut).trans_le ((selected_iterate_strict f B hf t).monotone hcount)
  · intro k hk hgap t u ht hu hshift
    have htails := gap_tail_bounds lam mu lam' mu' k
    have htP := htails.1.trans ht
    have huQ := htails.2.1.trans hu
    have hSu : S ≤ u := htails.2.2.1.trans hu
    have hshift' : u < f^[k] t := by change u+S ≤ f^[k] t at hshift; omega
    obtain ⟨i,hi,hEi⟩ := entryExistenceOrbit f B hf lam mu t ha hl hmu hml htP
    obtain ⟨j,hj,hEj⟩ := entryExistenceOrbit f B hf lam' mu' u ha' hl' hmu' hml' huQ
    have hres := gap_reserves f B hf lam mu lam' mu' t i k ha ha' hl hl' hmu hml hml' hgap ht hi
    have hc := countLag f f B B hf hf lam' mu' lam mu u t j i k S ha' ha hl' hl hmu' hmu
      hml' hml huQ htP hS.2.1 hS.1 hj hi
    have hcount : j+k ≤ i := hc.2 (by
      rw [gap_initial_limit f lam' mu' u hl' hml']
      exact hres.2) (by
        intro a _
        have hSa := hSu.trans (iterate_self_le hstep a u)
        have hlt : f^[a] u < f^[a+k] t := by
          rw [Function.iterate_add_apply]
          exact had.1.iterate a hshift'
        have hmargin := selected_input_margin f B hf S (f^[a] u) (f^[a+k] t) hSa hlt
        simpa only [Function.iterate_succ_apply'] using hmargin)
    refine ⟨i,j,hi,hj,hcount,?_⟩
    rw [hEj,hEi]
    have hlt : f^[j] u < f^[j+k] t := by
      rw [Function.iterate_add_apply]
      exact had.1.iterate j hshift'
    exact hlt.trans_le ((selected_iterate_strict f B hf t).monotone hcount)

end LogicLineages.PermittedControl
