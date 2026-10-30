module
public import LogicLineages.OrdinalComparison.ReserveEndpointTargets
public import LogicLineages.OrdinalComparison.ControlSegmentProof
public import LogicLineages.OrdinalComparison.ControlScheduleProof
public import LogicLineages.OrdinalComparison.ActualTerminal

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualPhiEndpointAlongTrace : Targets.ActualPhiEndpointAlongTrace := by
  intro A he i hi
  let S := actualControlledStateAfter Phi A i
  have hs := (actualControlledTraceFirstFinite Phi A he).2 i hi
  have hc := actualControlledCountTraceDecomposition Phi A he i hi
  have hn := actualControlledNormIteration Phi A he i hi
  have hA := (actualTerminalValueIdentities A he).2
  have hS := (actualTerminalValueIdentities S hs.1).2
  rw [← actualControlledCountPhiAgreement A he] at hA
  rw [← actualControlledCountPhiAgreement S hs.1] at hS
  rw [hS, hA, hc, hn, Function.iterate_add_apply]

theorem actualCompensatedExitDominatesTerminal : Targets.ActualCompensatedExitDominatesTerminal := by
  intro A he c
  dsimp only
  let g := compensatedPrefixControl c
  have hg := compensatedPrefixControlBounds c
  have hc := actualControlledCountsJointMonotone Phi g (fun n => (hg.2 n).1) hg.1
    A A le_rfl he le_rfl
  have hn := actualControlledNormIteration g A he (actualControlledCount g A) le_rfl
  have hvalue := (actualTerminalValueIdentities A he).2
  rw [← actualControlledCountPhiAgreement A he] at hvalue
  have hiter : ∀ i : Nat, (Phi^[i]) (actualOrdinalNorm A) ≤ (g^[i]) (actualOrdinalNorm A) := by
    intro i
    induction i with
    | zero => exact le_rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (Phi_strictMono.monotone ih).trans (hg.2 _).1
  have htime := (Phi_strictMono.strictMono_iterate_of_lt_map (self_lt_Phi (actualOrdinalNorm A))).monotone hc
  rw [hvalue, hn]
  exact htime.trans (hiter _)

end LogicLineages.OrdinalComparison
