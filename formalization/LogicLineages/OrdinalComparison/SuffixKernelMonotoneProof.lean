module
public import LogicLineages.OrdinalComparison.SuffixKernelMonotoneTargets
public import LogicLineages.OrdinalComparison.SuffixKernelProof
public import LogicLineages.OrdinalComparison.ActualTailSeparation

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualSuffixCountInputMassMonotone : Targets.ActualSuffixCountInputMassMonotone := by
  intro beta hb he a b t u hab htu ht hu
  let pi := Ordinal.omega0 ^ beta
  let I := actualSuffixKernelInitial pi b t
  let J := actualSuffixKernelInitial pi a u
  let g := compensatedPrefixControl b
  let h := compensatedPrefixControl a
  let E := actualSuffixKernelCount pi b t
  let F := actualSuffixKernelCount pi a u
  let lo := actualControlledStateAfter g I
  let hi := actualControlledStateAfter h J
  have hin := actualSuffixKernelInput beta hb he b t ht
  have hjn := actualSuffixKernelInput beta hb he a u hu
  have hlt := actualSuffixKernelTrace beta hb he b t ht
  have hht := actualSuffixKernelTrace beta hb he a u hu
  have hlo := actualControlledTraceFirstFinite g I hin.1
  have hhi := actualControlledTraceFirstFinite h J hjn.1
  have htrace : ∀ i : Nat, i ≤ E → i ≤ F → lo i ≤ hi i := by
    intro i
    induction i with
    | zero =>
      intro _ _
      change pi + ((t - b - actualOrdinalNorm pi : Nat) : Ordinal) ≤
        pi + ((u - a - actualOrdinalNorm pi : Nat) : Ordinal)
      apply add_le_add_right
      exact_mod_cast (show t - b - actualOrdinalNorm pi ≤ u - a - actualOrdinalNorm pi by omega)
    | succ i ih =>
      intro hiE hiF
      have hiEl : i < E := by omega
      have hiFl : i < F := by omega
      have hslo := hlo.2 i hiEl.le
      have hshi := hhi.2 i hiFl.le
      have hcomp := ih hiEl.le hiFl.le
      have hnlo := hlt.2.1 i hiEl.le
      have hnhi := hht.2.1 i hiFl.le
      change b + actualOrdinalNorm (lo i) = (Phi^[i]) t at hnlo
      change a + actualOrdinalNorm (hi i) = (Phi^[i]) u at hnhi
      have hbud : g (actualOrdinalNorm (lo i)) ≤ h (actualOrdinalNorm (hi i)) := by
        change Phi (b + actualOrdinalNorm (lo i)) - b ≤ Phi (a + actualOrdinalNorm (hi i)) - a
        rw [hnlo, hnhi]
        have hiter := (Phi_strictMono.iterate i).monotone htu
        have hp := Phi_strictMono.monotone hiter
        omega
      have hdlo := actualNonfiniteDecomposition (lo i) (hslo.2.2 hiEl) hslo.1
      have hdhi := actualNonfiniteDecomposition (hi i) (hshi.2.2 hiFl) hshi.1
      change actualControlledStateAfter g I (i + 1) ≤ actualControlledStateAfter h J (i + 1)
      rw [actualControlledStateAfter_succ, actualControlledStateAfter_succ]
      exact actualMaximumJointMonotone _ _ hdlo.2.1.bot_lt
        (actualLimitPartMonotone hcomp) hdhi.1 _ _ hbud
  change E ≤ F
  by_contra hn
  have hFE : F < E := by omega
  have hstates := htrace F hFE.le le_rfl
  have hnon : Ordinal.omega0 ≤ lo F := (hlo.2 F hFE.le).2.2 hFE
  have hfin : hi F < Ordinal.omega0 := hhi.1
  exact not_lt_of_ge (hnon.trans hstates) hfin

theorem actualSuffixKernelInputMassMonotone : Targets.ActualSuffixKernelInputMassMonotone := by
  intro beta hb he a b t u hab htu ht hu
  have hc := actualSuffixCountInputMassMonotone beta hb he a b t u hab htu ht hu
  have hcount : Monotone (fun n : Nat => (Phi^[n]) u) :=
    (Phi_strictMono.strictMono_iterate_of_lt_map (self_lt_Phi u)).monotone
  exact ((Phi_strictMono.iterate _).monotone htu).trans (hcount hc)

theorem actualSuffixKernelStrictInput : Targets.ActualSuffixKernelStrictInput := by
  intro beta hb he a b t u hab htu ht hu
  have hc := actualSuffixCountInputMassMonotone beta hb he a b t u hab htu.le ht hu
  have hcount : Monotone (fun n : Nat => (Phi^[n]) u) :=
    (Phi_strictMono.strictMono_iterate_of_lt_map (self_lt_Phi u)).monotone
  exact ((Phi_strictMono.iterate _) htu).trans_le (hcount hc)

end LogicLineages.OrdinalComparison
