module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedRevisionEventual
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionEventualProof
open GorbowSyntax GorbowSortedSyntaxCode GorbowPACore GorbowSortedRevision GorbowSortedRevisionEventual

private theorem knowledgeAt (g : Ground) (P : Extension) (σ : Sentence) :
    (allAgentsKnow σ).realize (interpretation g P) Fin.elim0 ↔ P (formulaCode σ) := by
  simp [allAgentsKnow,Formula.realize,Term.realize,numeral_realize,formulaQuote,interpretation,GorbowRevisionSemantics.interpretation]

theorem knowledgeCalibration : Comparators.GorbowSortedRevisionEventual.KnowledgeCalibration := by
  intro g initial n σ
  have hk := knowledgeAt g (extensions g initial n) σ
  have hs := (GorbowSortedRevisionProof.successorCalibration g initial n σ).2.1
  constructor
  · simpa [allKnowledgeSentence,Formula.realize,numeral_realize,stage,formulaQuote,interpretation,GorbowRevisionSemantics.interpretation] using hk
  · exact (knowledgeAt g (extensions g initial (n+1)) σ).trans (by
      simpa [allKnowledgeSentence,Formula.realize,numeral_realize,stage,formulaQuote,interpretation,GorbowRevisionSemantics.interpretation] using hs)

theorem ruleThresholds : Comparators.GorbowSortedRevisionEventual.RuleThresholds := by
  intro g initial σ N
  refine ⟨?_,?_,?_⟩
  · intro h n hn
    cases n with
    | zero => omega
    | succ n =>
      exact (GorbowSortedRevisionProof.successorCalibration g initial n σ).1.mpr (h n (by omega))
  · intro h n hn
    exact (GorbowSortedRevisionProof.successorCalibration g initial n σ).1.mp (h (n+1) (by omega))
  · intro h n hn
    cases n with
    | zero => omega
    | succ n =>
      exact (knowledgeCalibration g initial n σ).2.mpr (h n (by omega))

theorem modusPonens : Comparators.GorbowSortedRevisionEventual.ModusPonens := by
  intro g initial σ τ N M hi hs n hn
  exact hi n (le_trans (le_max_left N M) hn) (hs n (le_trans (le_max_right N M) hn))

private theorem raiseThreshold {g : Ground} {initial : Extension} {σ : Sentence} {N M : Nat}
    (h : Threshold g initial σ N) (hnm : N≤M) : Threshold g initial σ M :=
  fun n hn => h n (le_trans hnm hn)

theorem finiteThreshold : Comparators.GorbowSortedRevisionEventual.FiniteThreshold := by
  intro g initial sentences
  induction sentences with
  | nil => intro _; exact ⟨0,by simp⟩
  | cons σ rest ih =>
    intro h
    obtain ⟨N,hN⟩ := h σ (by simp)
    obtain ⟨M,hM⟩ := ih (fun τ ht => h τ (by simp [ht]))
    refine ⟨max N M,?_⟩
    intro τ ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact raiseThreshold hN (le_max_left N M)
    · exact raiseThreshold (hM τ ht) (le_max_right N M)

theorem coreThreshold : Comparators.GorbowSortedRevisionEventual.CoreThreshold := by
  intro g initial σ p n _
  exact GorbowSortedRevisionProof.coreSoundness g initial n 0 σ p Fin.elim0

theorem neverContradiction : Comparators.GorbowSortedRevisionEventual.NeverContradiction := by
  intro g initial h
  obtain ⟨N,hN⟩ := h
  exact falseEquality_not_realized (stage g initial N) (hN N (le_refl N))

theorem eventualRules : Comparators.GorbowSortedRevisionEventual.EventualRules := by
  intro g initial σ
  refine ⟨?_,?_,?_⟩
  · rintro ⟨N,h⟩
    exact ⟨N+1,(ruleThresholds g initial σ N).1 h⟩
  · rintro ⟨N,h⟩
    exact ⟨N,(ruleThresholds g initial σ N).2.1 h⟩
  · rintro ⟨N,h⟩
    exact ⟨N+1,(ruleThresholds g initial σ N).2.2 h⟩

theorem gorbowSortedRevisionEventual : Comparators.GorbowSortedRevisionEventual.Target :=
  ⟨knowledgeCalibration,ruleThresholds,modusPonens,finiteThreshold,coreThreshold,neverContradiction,eventualRules⟩
end LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionEventualProof
