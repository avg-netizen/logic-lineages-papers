module
public import LogicLineages.OrdinalComparison.SuffixKernelTargets
public import LogicLineages.OrdinalComparison.PrefixTraceBasicProof
public import LogicLineages.OrdinalComparison.ActualCollapseBounds
public import LogicLineages.OrdinalComparison.Control

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualSuffixKernelInput : Targets.ActualSuffixKernelInput := by
  intro beta hb he a t ht
  have hf := actualFiniteTailClosureNorm (Ordinal.omega0 ^ beta) he
    (t - a - actualOrdinalNorm (Ordinal.omega0 ^ beta))
  have hlim := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hb)
  refine ⟨hf.1, (Ordinal.omega0_le_of_isSuccLimit hlim).trans le_self_add, ?_⟩
  unfold actualSuffixKernelInitial
  rw [hf.2]
  omega

theorem actualSuffixKernelTrace : Targets.ActualSuffixKernelTrace := by
  intro beta hb he a t ht
  let pi := Ordinal.omega0 ^ beta
  let I := actualSuffixKernelInitial pi a t
  let E := actualSuffixKernelCount pi a t
  let state := actualControlledStateAfter (compensatedPrefixControl a) I
  have hin := actualSuffixKernelInput beta hb he a t ht
  have htr := actualControlledTraceFirstFinite (compensatedPrefixControl a) I hin.1
  have hpos : 0 < E := by
    by_contra hn
    have hz : E = 0 := by omega
    have hf : state E < Ordinal.omega0 := htr.1
    rw [hz] at hf
    exact (not_lt_of_ge hin.2.1) hf
  have hnorm : ∀ i : Nat, i ≤ E → a + actualOrdinalNorm (state i) = (Phi^[i]) t := by
    intro i
    induction i with
    | zero => intro _; exact hin.2.2
    | succ i ih =>
      intro hi
      have hiE : i < E := by omega
      have hs := htr.2 i (Nat.le_of_lt hiE)
      have hstep := actualControlledStepNorm (compensatedPrefixControl a) (state i)
        (hs.2.2 hiE) hs.1
      have hbound : a ≤ Phi (a + actualOrdinalNorm (state i)) := by
        have := self_lt_Phi (a + actualOrdinalNorm (state i))
        omega
      change a + actualOrdinalNorm
        ((actualControlledStep (compensatedPrefixControl a))^[i + 1] I) = _
      rw [Function.iterate_succ_apply']
      change a + actualOrdinalNorm (actualControlledStep (compensatedPrefixControl a) (state i)) = _
      rw [hstep]
      unfold compensatedPrefixControl
      rw [Nat.add_sub_of_le hbound, ih (by omega), Function.iterate_succ_apply']
  refine ⟨hpos, hnorm, htr.1, ?_, ?_, ?_⟩
  · intro i hi
    exact (htr.2 i (Nat.le_of_lt hi)).2.2 hi
  · have hn := hnorm E le_rfl
    change actualOrdinalNorm (state E) = (Phi^[E]) t - a
    omega
  · refine ⟨(Phi^[E - 1]) t, ?_⟩
    change Phi ((Phi^[E - 1]) t) = (Phi^[E]) t
    conv_rhs => rw [show E = (E - 1) + 1 by omega, Function.iterate_succ_apply']

end LogicLineages.OrdinalComparison
