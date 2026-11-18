module
public import LogicLineages.PermittedControl.TargetVisitTargets
public import LogicLineages.PermittedControl.CountLagTrajectoryProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem relative_target_guard (f : Nat → Nat) (a mu rho : Ordinal.{0}) (tau i : Nat)
    (ha : a < epsilonZero) (hrho : Order.IsSuccLimit rho)
    (hhit : FirstEntry f a (mu+rho) tau) (hi : i ≤ tau) :
    rho ≤ actualLimitPart ((descentWith f)^[i] a-mu) ∧
    (actualLimitPart ((descentWith f)^[i] a-mu)=rho ↔ i=tau) := by
  let z := (descentWith f)^[i] a
  let y := z-mu
  have htarget : mu+rho ≤ z := hhit.1.trans (trajectory_antitone f a ha hi)
  have hmuz : mu ≤ z := (le_self_add : mu ≤ mu+rho).trans htarget
  have hrec : z=mu+y := (Ordinal.add_sub_cancel_of_le hmuz).symm
  have hry : rho ≤ y := (Ordinal.le_sub_of_le hmuz).mpr htarget
  have hy : y < epsilonZero := (Ordinal.sub_le_self z mu).trans_lt (trajectory_below f a ha i)
  have hnon : Ordinal.omega0 ≤ y := (Ordinal.omega0_le_of_isSuccLimit hrho).trans hry
  have hd := actualNonfiniteDecomposition y hnon hy
  have hlim : actualLimitPart z=mu+actualLimitPart y := by
    conv_lhs => rw [hrec,hd.2.2.1,← add_assoc]
    exact limitPart_tail _ (Ordinal.isSuccLimit_add mu hd.2.1) _
  have hfixed : actualLimitPart rho=rho := by simpa using limitPart_tail rho hrho 0
  have hbound := actualLimitPartMonotone hry
  rw [hfixed] at hbound
  refine ⟨hbound, ?_⟩
  constructor
  · intro heq
    have hz : actualLimitPart z=mu+rho := by rw [hlim]; exact congrArg (fun x : Ordinal => mu+x) heq
    have henter := (interval_iff_limitPart z (mu+rho) (Or.inr (Ordinal.isSuccLimit_add mu hrho))).mpr hz
    by_contra hne
    exact hhit.2.2 i (lt_of_le_of_ne hi hne) henter
  · intro heq
    subst i
    have hz := (interval_iff_limitPart ((descentWith f)^[tau] a) (mu+rho)
      (Or.inr (Ordinal.isSuccLimit_add mu hrho))).mp ⟨hhit.1,hhit.2.1⟩
    change actualLimitPart z=mu+rho at hz
    rw [hlim] at hz
    exact add_left_cancel hz

 theorem actual_entry_reset (f : Nat → Nat) (a target : Ordinal.{0}) (i E : Nat)
    (htarget : target < epsilonZero) (hhit : FirstEntry f a target i)
    (hE : entryNormAt f a i=E) :
    (descentWith f)^[i] a = countInitial target E := by
  obtain ⟨n,heq⟩ := interval_tail ((descentWith f)^[i] a) target hhit.1 hhit.2.1
  have hn : actualOrdinalNorm target+n=E := by
    rw [← (actualFiniteTailClosureNorm target htarget n).2,← heq]
    exact hE
  have hsub : E-actualOrdinalNorm target=n := by omega
  rw [heq]
  simp only [countInitial,hsub]

 theorem actual_entry_reset_continuation (f : Nat → Nat) (a target : Ordinal.{0}) (i E k : Nat)
    (htarget : target < epsilonZero) (hhit : FirstEntry f a target i)
    (hE : entryNormAt f a i=E) :
    (descentWith f)^[i+k] a = (descentWith f)^[k] (countInitial target E) := by
  rw [Nat.add_comm i k, Function.iterate_add_apply, actual_entry_reset f a target i E htarget hhit hE]

 theorem synchronizedTargetVisits : Targets.SynchronizedTargetVisits := by
  intro f B hf mu nu sigma rho t hmu hnu hs hr hmud hnud hsl hrl hrs ht
  have had := selected_threshold_admissible f B hf
  have hA := epsilonZero_add_principal hmu hs
  have hA' := epsilonZero_add_principal hnu hs
  have hT := epsilonZero_add_principal hmu hr
  have hT' := epsilonZero_add_principal hnu hr
  have hAl := Ordinal.isSuccLimit_add mu hsl
  have hAl' := Ordinal.isSuccLimit_add nu hsl
  have hTl := Ordinal.isSuccLimit_add mu hrl
  have hTl' := Ordinal.isSuccLimit_add nu hrl
  have hin := count_initial_facts (mu+sigma) t hA hAl (by omega)
  have hin' := count_initial_facts (nu+sigma) t hA' hAl' (by omega)
  have hlow : mu+rho ≤ countInitial (mu+sigma) t :=
    ((add_le_add_iff_left mu).mpr hrs).trans le_self_add
  have hlow' : nu+rho ≤ countInitial (nu+sigma) t :=
    ((add_le_add_iff_left nu).mpr hrs).trans le_self_add
  obtain ⟨i,hi,hEi⟩ := entry_exists_state f had.2 (mu+rho) (Or.inr hTl)
    (countInitial (mu+sigma) t) hin.1 hlow (by rw [hin.2.1]; omega)
  obtain ⟨j,hj,hEj⟩ := entry_exists_state f had.2 (nu+rho) (Or.inr hTl')
    (countInitial (nu+sigma) t) hin'.1 hlow' (by rw [hin'.2.1]; omega)
  rw [hin.2.1] at hEi
  rw [hin'.2.1] at hEj
  have hguard : ∀ h : Nat, h ≤ i → rho ≤ actualLimitPart (relativeState f (mu+sigma) mu t h) ∧
      (actualLimitPart (relativeState f (mu+sigma) mu t h)=rho ↔ h=i) := by
    intro h hh
    exact relative_target_guard f _ mu rho i h hin.1 hrl hi hh
  have hguard' : ∀ h : Nat, h ≤ j → rho ≤ actualLimitPart (relativeState f (nu+sigma) nu t h) ∧
      (actualLimitPart (relativeState f (nu+sigma) nu t h)=rho ↔ h=j) := by
    intro h hh
    exact relative_target_guard f _ nu rho j h hin'.1 hrl hj hh
  refine ⟨i,j,hi,hj,hEi,hEj,hguard,hguard',?_,?_⟩
  · intro heq
    subst j
    exact ⟨actual_entry_reset f _ _ i _ hT hi hEi, actual_entry_reset f _ _ i _ hT' hj hEj⟩
  · intro hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · refine ⟨i, (Nat.min_eq_left hij.le).symm, ?_, (hguard i le_rfl).1, (hguard' i hij.le).1⟩
      intro heq
      have hp := (hguard i le_rfl).2.mpr rfl
      have he := (hguard' i hij.le).2.mp (heq.symm.trans hp)
      omega
    · refine ⟨j, (Nat.min_eq_right hji.le).symm, ?_, (hguard j hji.le).1, (hguard' j le_rfl).1⟩
      intro heq
      have hp := (hguard' j le_rfl).2.mpr rfl
      have he := (hguard j hji.le).2.mp (heq.trans hp)
      omega

end LogicLineages.PermittedControl
