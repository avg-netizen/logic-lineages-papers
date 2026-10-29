module
public import LogicLineages.OrdinalComparison.ActualLimitPredecessorTargets
public import LogicLineages.OrdinalComparison.ActualMaximumPredecessor
public import LogicLineages.OrdinalComparison.LimitPredecessor

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualLimitMaximumPredecessorSaturation :
    Targets.ActualLimitMaximumPredecessorSaturation := by
  intro a ha hlim b
  obtain ⟨n, hn⟩ := normalRepresentationComplete a ha
  have hnlim : Order.IsSuccLimit n.1.repr := by rwa [hn]
  have hnpos : (0 : NONote) < n := hnlim.bot_lt
  rw [← hn, ← actualMaximumPredecessor_notationCorrespondence n hnpos b,
    actualOrdinalNorm_notationCorrespondence]
  exact limitMaximumPredecessorSaturation n hnlim b

theorem actualLimitMaximumPredecessorStrictGrowth :
    Targets.ActualLimitMaximumPredecessorStrictGrowth := by
  intro a ha hlim b c hbc
  obtain ⟨n, hn⟩ := normalRepresentationComplete a ha
  have hnlim : Order.IsSuccLimit n.1.repr := by rwa [hn]
  have hnpos : (0 : NONote) < n := hnlim.bot_lt
  rw [← hn, ← actualMaximumPredecessor_notationCorrespondence n hnpos b,
    ← actualMaximumPredecessor_notationCorrespondence n hnpos c]
  exact limitMaximumPredecessorStrictGrowth n hnlim hbc

end LogicLineages.OrdinalComparison
