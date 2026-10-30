module
public import LogicLineages.OrdinalComparison.HeadEndpointTargets
public import LogicLineages.OrdinalComparison.PrefixTraceBasicProof
public import LogicLineages.OrdinalComparison.ActualTerminal
public import LogicLineages.OrdinalComparison.ActualCollapseBounds

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualHeadInputFacts : Targets.ActualHeadInputFacts := by
  intro lam hlam hlimit t ht
  have hf := actualFiniteTailClosureNorm lam hlam (t - actualOrdinalNorm lam)
  refine ⟨hf.1, (Ordinal.omega0_le_of_isSuccLimit hlimit).trans le_self_add, ?_⟩
  change actualOrdinalNorm (lam + ((t - actualOrdinalNorm lam : Nat) : Ordinal)) = t
  rw [hf.2, Nat.add_sub_of_le ht]

theorem actualHeadCompleteCount : Targets.ActualHeadCompleteCount := by
  intro lam hlam hlimit t ht
  have hi := actualHeadInputFacts lam hlam hlimit t ht
  have hcount := actualControlledCountPhiAgreement (actualHeadInitial lam t) hi.1
  have hterminal := actualTerminalFirstFinite (actualHeadInitial lam t) hi.1
  have hids := actualTerminalValueIdentities (actualHeadInitial lam t) hi.1
  have hdecomp := actualCompleteTerminalDecomposition lam hlam hlimit t ht
  have hpos : 0 < actualHeadCount lam t := hdecomp.2.2.1
  have hvalue : actualHeadValue lam t = actualHeadEndpoint lam t + actualHeadCount lam t := hids.1
  have hendpoint : actualHeadEndpoint lam t = (Phi^[actualHeadCount lam t]) t := by
    have h := hids.2
    rw [hi.2.2] at h
    exact h
  refine ⟨hcount, hpos, ?_, ?_, hendpoint, hvalue⟩
  · exact hterminal.1
  · exact hterminal.2

theorem fullActualHeadCompleteCount : Targets.FullActualHeadCompleteCount :=
  ⟨actualHeadInputFacts, actualHeadCompleteCount⟩

end LogicLineages.OrdinalComparison
