module
public import LogicLineages.PermittedControl.SensitiveUnitTargets
public import LogicLineages.PermittedControl.ThickBlockProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem sensitive_tail_large (R B t : Nat) (ht : thickBlockTail R B ≤ t) : R+3 ≤ t := by
  have hb : 100*(R+2)^4 ≤ t := (le_max_left _ _).trans ht
  have hpow : R+2 ≤ (R+2)^4 := Nat.le_self_pow (by omega : 4 ≠ 0) (R+2)
  omega

 theorem quadraticUnitTop : Targets.QuadraticUnitTop := by
  intro f B mu nu P A A' R t hsetup
  rcases hsetup with ⟨hf,hmu,hnu,hP,ha,hA,hA',hmud,hnud,hPpos,h2,hdiv,hr,hrd,
    hR,hmuR,hnuR,hPR,haR,ht,hpart,hpart',hnorm,hnorm',hcd⟩
  let c := relativeProfile mu (Ordinal.log Ordinal.omega0 P)
  let d := relativeProfile nu (Ordinal.log Ordinal.omega0 P)
  let u := f t
  let X := u-c-actualOrdinalNorm P
  let Y := u-d-actualOrdinalNorm P
  have hcR : c ≤ R := (relativePrefixNorm mu _ hmu).2.2.trans hmuR
  have hdR : d ≤ R := (relativePrefixNorm nu _ hnu).2.2.trans hnuR
  have hlarge := sensitive_tail_large R B t ht
  have hu : 2*t+4 ≤ u := (G_large t).trans ((selected_threshold_admissible f B hf).2 t)
  have hX : 2 ≤ X := by dsimp [X]; omega
  have hY : 2 ≤ Y := by dsimp [Y]; omega
  have hYX : Y < X := by dsimp [X,Y,c,d] at *; omega
  have heven : 2 ∣ u := selected_even f B hf t
  have hlocal := retainedLocalPhase mu P 2 u hmu hP ha hPpos (by norm_num) hdiv
    (by omega) (by change c+actualOrdinalNorm P<u; omega)
  have hlocal' := retainedLocalPhase nu P 2 u hnu hP ha hPpos (by norm_num) hdiv
    (by omega) (by change d+actualOrdinalNorm P<u; omega)
  have hnext : descentWith f A-mu = P+actualMaximumPredecessor (Ordinal.omega0^(2 : Ordinal.{0})) X := by
    unfold descentWith
    rw [hpart,hnorm]
    simpa only [add_zero] using hlocal
  have hnext' : descentWith f A'-nu = P+actualMaximumPredecessor (Ordinal.omega0^(2 : Ordinal.{0})) Y := by
    unfold descentWith
    rw [hpart',hnorm']
    simpa only [add_zero] using hlocal'
  have hp2 := phase_power_below (2 : Ordinal.{0}) ha
  have hsmall : Ordinal.omega0 < Ordinal.omega0^(2 : Ordinal) := by
    simpa using (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono (show (1 : Ordinal.{0})<2 by norm_num)
  have hNW : actualOrdinalNorm Ordinal.omega0=2 := by simpa using actualFiniteHeadNorm 1 0
  have hbound : ∀ b : Nat, 2 ≤ b → Ordinal.omega0 ≤ actualMaximumPredecessor (Ordinal.omega0^(2 : Ordinal.{0})) b := by
    intro b hb
    exact (actualMaximumPredecessor_correct _ (Ordinal.opow_pos _ Ordinal.omega0_pos) hp2 b).2 ⟨hsmall,by rwa [hNW]⟩
  have hbX := (actualMaximumPredecessor_correct _ (Ordinal.opow_pos _ Ordinal.omega0_pos) hp2 X).1.1.trans hp2
  have hbY := (actualMaximumPredecessor_correct _ (Ordinal.opow_pos _ Ordinal.omega0_pos) hp2 Y).1.1.trans hp2
  rw [hnext,hnext',phase_limit_add P _ hbX (hbound X hX),phase_limit_add P _ hbY (hbound Y hY),
    add_left_cancel_iff,quadraticLocalCoincidence X Y hX hY (ne_of_gt hYX),max_eq_left hYX.le,min_eq_right hYX.le]
  change X=Y+1 ∧ X%2=1 ↔ d=c+1 ∧ (c+actualOrdinalNorm P)%2=1
  have hu0 : u%2=0 := Nat.mod_eq_zero_of_dvd heven
  dsimp [X,Y]
  omega

end LogicLineages.PermittedControl
