module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RankTargets
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RowProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.Proof
open PolynomialGraphCompletion OuterShiftNormalization

theorem actualResidualHeads : RankTargets.ActualResidualHeads := by
  intro n c
  induction n with
  | zero =>
      intro p hp
      simp only [residualWords,List.mem_singleton] at hp
      subst p
      exact ⟨[],rfl⟩
  | succ n ih =>
      intro p hp
      simp only [residualWords,List.mem_cons,List.mem_map] at hp
      rcases hp with rfl | ⟨q,hq,rfl⟩
      · exact ⟨[],rfl⟩
      · obtain ⟨B,hB⟩ := ih q hq
        refine ⟨kernelLetter (n+4) (c+n+4) 0 :: B,?_⟩
        simp only [hB,List.cons_append]

private theorem splitWord_append_nonshift (A : Word) (a : Letter) (ha : a.1 ≠ 0) :
    splitWord (A++[a]) = (A++[a],[]) := by
  induction A with
  | nil => simp [splitWord,splitStep,ha]
  | cons b A ih =>
      change splitStep b (splitWord (A++[a])) = (b::(A++[a]),[])
      rw [ih]
      simp [splitStep]

theorem actualResidualTopRanks : RankTargets.ActualResidualTopRanks := by
  intro n c p hp A
  obtain ⟨B,hB⟩ := actualResidualHeads n c p hp
  rw [hB,← List.append_assoc]
  constructor
  · simp [topRank,List.getLastD_concat,counterLetter]
  · exact congrArg Prod.fst
      (splitWord_append_nonshift (A++B) (counterLetter p.1 (c+p.1))
        (by simp [counterLetter]))

theorem residualRowRankBounds : RankTargets.ResidualRowRankBounds := by
  intro D a i A n c hD r hr
  obtain ⟨b,hb,hr⟩ := List.mem_map.mp hr
  have hb' := (List.mem_filter.mp hb).1
  change b ∈ (residualWords n c).map (fun p => (2*a,i,A++p.2)) at hb'
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb'
  have hs := (residualWordSyntax D n c hD).2 p hp
  have hh := actualResidualTopRanks n c p hp A
  rw [hh.2,hh.1] at hr
  constructor <;> omega

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.Proof
