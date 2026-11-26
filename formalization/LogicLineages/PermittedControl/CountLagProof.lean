module
public import LogicLineages.PermittedControl.CountLagTrajectoryProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem countLag : Targets.CountLag := by
  intro f g B C hf hg lam mu lam' mu' t u tau sigma k S ha ha' hl hl' hmu hmu' hml hml'
    ht hu hmuS hmuS' hhit hhit'
  have had := selected_threshold_admissible f B hf
  have had' := selected_threshold_admissible g C hg
  have hin := count_initial_facts lam t ha hl (by omega)
  have hin' := count_initial_facts lam' u ha' hl' (by omega)
  have hdata := entry_trajectory_data f B hf lam mu t tau ha hl hmu hml ht hhit
  have hdata' := entry_trajectory_data g C hg lam' mu' u sigma ha' hl' hmu' hml' hu hhit'
  have hpos := relative_positive_iff f B hf lam mu t tau ha hl hmu hml ht hhit
  have hpos' := relative_positive_iff g C hg lam' mu' u sigma ha' hl' hmu' hml' hu hhit'
  have htau : 0 < tau := proper_entry_pos f lam mu t tau hl hml hhit
  have hdom : ∀ i : Nat, i ≤ tau → mu+relativeState f lam mu t i < epsilonZero := by
    intro i hi
    rw [← (hdata.1 i hi).1]
    exact trajectory_below f _ hin.1 i
  have hdom' : ∀ j : Nat, j ≤ sigma → mu'+relativeState g lam' mu' u j < epsilonZero := by
    intro j hj
    rw [← (hdata'.1 j hj).1]
    exact trajectory_below g _ hin'.1 j
  have hbudget : ∀ i : Nat, actualOrdinalNorm mu ≤ f^[i] t := by
    intro i
    exact (show actualOrdinalNorm mu ≤ t by omega).trans
      (iterate_self_le (control_self_le f had.2) i t)
  constructor
  · intro hinit hslack
    have inv : ∀ i : Nat, i ≤ tau →
        actualLimitPart (relativeState f lam mu t i) <
          actualLimitPart (relativeState g lam' mu' u (i+k)) ∧ i+k < sigma := by
      intro i
      induction i with
      | zero =>
        intro _
        refine ⟨by simpa using hinit, ?_⟩
        simpa using (hpos' k).mp (((hpos 0).mpr htau).trans hinit)
      | succ i ih =>
        intro hi
        have hit : i < tau := by omega
        obtain ⟨hcmp, hrun⟩ := ih hit.le
        have hstep := strictPropagation mu mu' (relativeState f lam mu t i)
          (relativeState g lam' mu' u (i+k)) S (f^[i] t) (f^[i+1] t) (g^[i+k+1] u)
          (hdom i hit.le) (hdom' (i+k) hrun.le) hmuS hmuS'
          (hdata.1 i hit.le).2.2.1 (hbudget (i+1)) ((hpos i).mpr hit) hcmp (hslack i hit)
        have hcompnext : actualLimitPart (relativeState f lam mu t (i+1)) <
            actualLimitPart (relativeState g lam' mu' u (i+k+1)) := by
          rw [hdata.2 i hit, hdata'.2 (i+k) hrun]
          exact hstep.2.trans_le hstep.1
        have hupperpos : 0 < actualLimitPart (relativeState g lam' mu' u (i+k+1)) := by
          rw [hdata'.2 (i+k) hrun]
          exact ((hpos i).mpr hit).trans_le hstep.1
        have hcount := (hpos' (i+k+1)).mp hupperpos
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using And.intro hcompnext hcount
    exact (inv tau le_rfl).2
  · intro hinit hslack
    have inv : ∀ i : Nat, i ≤ tau →
        actualLimitPart (relativeState f lam mu t i) ≤
          actualLimitPart (relativeState g lam' mu' u (i+k)) ∧ i+k ≤ sigma := by
      intro i
      induction i with
      | zero =>
        intro _
        refine ⟨by simpa using hinit, ?_⟩
        have hk := (hpos' k).mp (((hpos 0).mpr htau).trans_le hinit)
        simpa using hk.le
      | succ i ih =>
        intro hi
        have hit : i < tau := by omega
        obtain ⟨hcmp, hrunle⟩ := ih hit.le
        have hrun : i+k < sigma := (hpos' (i+k)).mp (((hpos i).mpr hit).trans_le hcmp)
        have hcompnext : actualLimitPart (relativeState f lam mu t (i+1)) ≤
            actualLimitPart (relativeState g lam' mu' u (i+k+1)) := by
          rw [hdata.2 i hit, hdata'.2 (i+k) hrun]
          rcases lt_or_eq_of_le hcmp with hstrict | heq
          · have hsmall : f^[i] t + S ≤ g^[i+k+1] u := by
              have hn := control_self_le f had.2 (f^[i] t)
              have hs := hslack i hit
              rw [Function.iterate_succ_apply'] at hs
              omega
            have hstep := strictPropagation mu mu' (relativeState f lam mu t i)
              (relativeState g lam' mu' u (i+k)) S (f^[i] t) (f^[i+1] t) (g^[i+k+1] u)
              (hdom i hit.le) (hdom' (i+k) hrun.le) hmuS hmuS'
              (hdata.1 i hit.le).2.2.1 (hbudget (i+1)) ((hpos i).mpr hit) hstrict hsmall
            exact hstep.2.le.trans hstep.1
          · exact weakPropagation mu mu' (relativeState f lam mu t i)
              (relativeState g lam' mu' u (i+k)) S (f^[i+1] t) (g^[i+k+1] u)
              (hdom i hit.le) (hdom' (i+k) hrun.le) hmuS hmuS'
              (hbudget (i+1)) ((hpos i).mpr hit) heq.symm (hslack i hit)
        have hcount : i+k+1 ≤ sigma := by omega
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using And.intro hcompnext hcount
    exact (inv tau le_rfl).2

end LogicLineages.PermittedControl
