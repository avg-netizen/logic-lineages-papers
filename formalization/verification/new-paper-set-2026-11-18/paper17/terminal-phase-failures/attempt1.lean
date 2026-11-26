module
public import LogicLineages.PermittedControl.TerminalPhaseTargets
public import LogicLineages.PermittedControl.PureMaximumBandProof
public import LogicLineages.PermittedControl.InitialClockProof
public import LogicLineages.OrdinalComparison.ActualFiniteHead

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem actualTerminalSquare : Targets.ActualTerminalSquare := by
  intro f B hf mu A R t hmu hA hmud hR hmuR ht hp hn
  let c := relativeProfile mu 1
  let q := (f t-c)/2
  have had := selected_threshold_admissible f B hf
  have hlarge := sensitive_tail_double R B t ht
  have hu := (G_large t).trans (had.2 t)
  have hc : c ≤ R := (relativePrefixNorm mu 1 hmu).2.2.trans hmuR
  have h1 : (1 : Ordinal.{0}) < epsilonZero := (Ordinal.natCast_lt_omega0 1).trans omega0_lt_epsilonZero
  have h2 : (2 : Ordinal.{0}) < epsilonZero := (Ordinal.natCast_lt_omega0 2).trans omega0_lt_epsilonZero
  have hw := phase_power_below 1 h1
  have hwn : actualOrdinalNorm Ordinal.omega0=2 := by simpa using actualFiniteHeadNorm 1 0
  have hcost := relativeNorm mu Ordinal.omega0 hmu (by simpa using hw)
  have hPb : actualOrdinalNorm (mu+Ordinal.omega0) ≤ f t := by omega
  have hmub : actualOrdinalNorm mu ≤ f t := by omega
  have hcal := pure_successor_maximum mu 1 (f t) hmu h1 hmub (by simpa using hPb)
  have hrel := relativeMaximumSpec mu (Ordinal.omega0^(2 : Ordinal)) (f t)
    (epsilonZero_add_principal hmu (phase_power_below 2 h2))
    (Ordinal.opow_pos _ Ordinal.omega0_pos) hmub
  have hnext : descentWith f A=mu+(Ordinal.omega0*(q : Ordinal)+((f t-c)%2 : Nat)) := by
    unfold descentWith
    rw [hp,hn,hrel.1]
    have hcal' : relativeMaximum mu (Ordinal.omega0^(2 : Ordinal)) (f t)=
      actualMaximumPredecessor (Ordinal.omega0^(2 : Ordinal)) (f t-c) := by simpa [c] using hcal
    rw [hcal',actualOmegaSquaredMaximum (f t-c) (by omega)]
  have hskip : mu+Ordinal.omega0 ≤ A := by
    have hw2 : Ordinal.omega0 ≤ Ordinal.omega0^(2 : Ordinal) := Ordinal.left_le_opow _ (by norm_num)
    exact (add_le_add_left hw2 mu).trans (by rw [←hp]; exact Ordinal.mul_div_le A Ordinal.omega0)
  have hhit : FirstEntry f A mu (1+q) := firstEntry_prepend f A mu q hskip (by
    rw [hnext]
    exact linear_entry f had.2 mu hmud hmu q ((f t-c)%2))
  obtain ⟨i,hi,hiN⟩ := entry_exists_state f had.2 mu hmud A hA
    (le_self_add.trans hskip) (by omega)
  have hiq := firstEntry_unique f A mu i (1+q) hi hhit
  subst i
  refine ⟨hhit,by simpa only [hn] using hiN,?_⟩
  have heven := selected_even f B hf t
  have he : f t%2=0 := Nat.mod_eq_zero_of_dvd heven
  dsimp only [q]
  omega

 theorem actualTerminalOmega : Targets.ActualTerminalOmega := by
  intro f B hf mu A t hmu hA hmud hp hn
  have had := selected_threshold_admissible f B hf
  have hlim := Ordinal.isSuccLimit_add mu Ordinal.isSuccLimit_omega0
  have hint := (interval_iff_limitPart A (mu+Ordinal.omega0) (Or.inr hlim)).mpr hp
  obtain ⟨n,heq⟩ := interval_tail A (mu+Ordinal.omega0) hint.1 hint.2
  have hhit : FirstEntry f A mu 1 := by
    rw [heq]
    simpa only [Nat.cast_one,mul_one,add_assoc] using linear_entry f had.2 mu hmud hmu 1 n
  refine ⟨hhit,?_⟩
  change actualOrdinalNorm (descentWith f A)=f t
  rw [descent_norm f A ((le_add_self : Ordinal.omega0 ≤ mu+Ordinal.omega0).trans hint.1) hA,hn]

 theorem actualTerminalSquareComparison : Targets.ActualTerminalSquareComparison := by
  intro f B hf mu nu A A' R t hmu hnu hA hA' hmud hnud hR hmuR hnuR ht hp hp' hn hn'
  have h := actualTerminalSquare f B hf mu A R t hmu hA hmud hR hmuR ht hp hn
  have h' := actualTerminalSquare f B hf nu A' R t hnu hA' hnud hR hnuR ht hp' hn'
  refine ⟨h.1,h'.1,?_⟩
  rw [h.2.1,h'.2.1,h.2.2,h'.2.2]
  have hs := selected_iterate_strict f B hf t
  have hc := (relativePrefixNorm mu 1 hmu).2.2.trans hmuR
  have hc' := (relativePrefixNorm nu 1 hnu).2.2.trans hnuR
  have ht' := sensitive_tail_double R B t ht
  have hu := (G_large t).trans ((selected_threshold_admissible f B hf).2 t)
  rcases lt_trichotomy ((relativeProfile nu 1+1)/2) ((relativeProfile mu 1+1)/2) with hlt | heq | hgt
  · rw [compare_eq_lt_iff.mpr hlt,compare_eq_lt_iff.mpr (hs (by omega))]
  · rw [heq]
    simp
  · rw [compare_eq_gt_iff.mpr hgt,compare_eq_gt_iff.mpr (hs (by omega))]

 theorem terminalPhaseFoundation : Targets.TerminalPhaseFoundation :=
  ⟨actualTerminalSquare,actualTerminalSquareComparison,actualTerminalOmega⟩
end LogicLineages.PermittedControl
