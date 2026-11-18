module
public import LogicLineages.PermittedControl.DivergenceEntryTargets
public import LogicLineages.PermittedControl.TerminalPhaseProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem positive_relative_phase (mu A : Ordinal.{0}) (hA : A < epsilonZero)
    (hp : 0 < actualLimitPart (A-mu)) :
    Order.IsSuccLimit (actualLimitPart A) ∧ mu < actualLimitPart A ∧ mu+Ordinal.omega0 ≤ A := by
  have hr := limitPart_zero_or_limit (A-mu)
  have hrl : Order.IsSuccLimit (actualLimitPart (A-mu)) := hr.resolve_left hp.ne'
  have hw := Ordinal.omega0_le_of_isSuccLimit hrl
  have hnon : Ordinal.omega0 ≤ A-mu := hw.trans (Ordinal.mul_div_le _ _)
  have he := absolute_limit_of_relative mu A hA hnon
  refine ⟨?_,?_,?_⟩
  · rw [he]
    exact Ordinal.isSuccLimit_add mu hrl
  · rw [he]
    exact (lt_add_iff_pos_right mu).mpr hp
  · exact (add_le_add_right hw mu).trans (by rw [←he]; exact Ordinal.mul_div_le _ _)

 theorem current_divergence_entries (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (mu nu A A' : Ordinal.{0}) (t : Nat)
    (hmu : mu < epsilonZero) (hnu : nu < epsilonZero) (hA : A < epsilonZero) (hA' : A' < epsilonZero)
    (hmud : mu=0 ∨ Order.IsSuccLimit mu) (hnud : nu=0 ∨ Order.IsSuccLimit nu)
    (hn : actualOrdinalNorm A=t) (hn' : actualOrdinalNorm A'=t)
    (hmuN : actualOrdinalNorm mu ≤ t) (hnuN : actualOrdinalNorm nu ≤ t)
    (hpos : 0 < actualLimitPart (A-mu))
    (hcmp : actualLimitPart (A-mu) < actualLimitPart (A'-nu)) :
    ∃ tau sigma : Nat, 0 < tau ∧ tau < sigma ∧ FirstEntry f A mu tau ∧ FirstEntry f A' nu sigma ∧
      entryNormAt f A tau=f^[tau] t ∧ entryNormAt f A' sigma=f^[sigma] t := by
  have had := selected_threshold_admissible f B hf
  have hphase := positive_relative_phase mu A hA hpos
  have hphase' := positive_relative_phase nu A' hA' (hpos.trans hcmp)
  have hl := (Ordinal.mul_div_le A Ordinal.omega0).trans_lt hA
  have hl' := (Ordinal.mul_div_le A' Ordinal.omega0).trans_lt hA'
  have hnorm := actual_limit_norm_le A _ hA hphase.1 rfl
  have hnorm' := actual_limit_norm_le A' _ hA' hphase'.1 rfl
  have htwo := nonfinite_norm A hA ((le_add_self : Ordinal.omega0 ≤ mu+Ordinal.omega0).trans hphase.2.2)
  have hreset := actual_phase_normalize f A (actualLimitPart A) t hl (Or.inr hphase.1) rfl hn
  have hreset' := actual_phase_normalize f A' (actualLimitPart A') t hl' (Or.inr hphase'.1) rfl hn'
  obtain ⟨tau,htau,hNtau⟩ := entry_exists_state f had.2 mu hmud A hA
    (le_self_add.trans hphase.2.2) (by omega)
  obtain ⟨sigma,hsigma,hNsigma⟩ := entry_exists_state f had.2 nu hnud A' hA'
    (le_self_add.trans hphase'.2.2) (by omega)
  have hct := countLag f f B B hf hf (actualLimitPart A) mu (actualLimitPart A') nu
    t t tau sigma 0 (max (actualOrdinalNorm mu) (actualOrdinalNorm nu)) hl hl' hphase.1 hphase'.1
    hmud hnud hphase.2.1 hphase'.2.1 (by omega) (by omega) (le_max_left _ _) (le_max_right _ _)
    (by rwa [←hreset]) (by rwa [←hreset'])
  have horder : tau < sigma := by
    apply Nat.add_zero tau ▸ hct.1 ?_ ?_
    · simpa only [relativeState,Function.iterate_zero_apply,←hreset,←hreset'] using hcmp
    · intro j hj
      have hjt := iterate_self_le (control_self_le f had.2) j t
      have hg := (G_large (f^[j] t)).trans (had.2 (f^[j] t))
      simp only [Nat.add_zero,Function.iterate_succ_apply']
      omega
  have htaupos : 0 < tau := by
    by_contra hh
    have : tau=0 := by omega
    subst tau
    exact (not_lt_of_ge hphase.2.2) htau.2.1
  exact ⟨tau,sigma,htaupos,horder,htau,hsigma,by simpa only [hn] using hNtau,by simpa only [hn'] using hNsigma⟩

 theorem actualDivergenceEntryOrder : Targets.ActualDivergenceEntryOrder := by
  intro f B hf mu nu A A' i t hmu hnu hA hA' hmud hnud hn hn' hmuN hnuN hpos hcmp
  have hiA := trajectory_below f A hA i
  have hiA' := trajectory_below f A' hA' i
  obtain ⟨p,q,hp,hpq,hpHit,hqHit,hpN,hqN⟩ := current_divergence_entries f B hf mu nu
    ((descentWith f)^[i] A) ((descentWith f)^[i] A') t hmu hnu hiA hiA' hmud hnud hn hn' hmuN hnuN hpos hcmp
  have hphase := positive_relative_phase mu _ hiA hpos
  have hphase' := positive_relative_phase nu _ hiA' (hpos.trans hcmp)
  have hhit : FirstEntry f A mu (i+p) := firstEntry_shift f A mu i p (by
    intro j hj hh
    exact (not_lt_of_ge (hphase.2.2.trans (trajectory_antitone f A hA hj.le))) hh.2) hpHit
  have hhit' : FirstEntry f A' nu (i+q) := firstEntry_shift f A' nu i q (by
    intro j hj hh
    exact (not_lt_of_ge (hphase'.2.2.trans (trajectory_antitone f A' hA' hj.le))) hh.2) hqHit
  have hN : entryNormAt f A (i+p)=f^[p] t := by
    simpa only [entryNormAt,Nat.add_comm i p,Function.iterate_add_apply] using hpN
  have hN' : entryNormAt f A' (i+q)=f^[q] t := by
    simpa only [entryNormAt,Nat.add_comm i q,Function.iterate_add_apply] using hqN
  refine ⟨i+p,i+q,by omega,by omega,hhit,hhit',?_,?_,?_⟩
  · simpa only [Nat.add_sub_cancel_left] using hN
  · simpa only [Nat.add_sub_cancel_left] using hN'
  · rw [hN,hN']
    exact selected_iterate_strict f B hf t hpq
end LogicLineages.PermittedControl
