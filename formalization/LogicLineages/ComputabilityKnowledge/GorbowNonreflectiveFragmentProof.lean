module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowNonreflectiveFragment
public import LogicLineages.ComputabilityKnowledge.GorbowAtomicTruthProof
public import LogicLineages.ComputabilityKnowledge.GorbowKnowledgeDispatchProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProofProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionEventualProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowNonreflectiveFragmentProof
open GorbowSyntax GorbowSortedRevision GorbowSortedRevisionEventual GorbowNonreflectiveFragment

private theorem knowledgePositive (initial : Extension) (k : Nat) :
    GorbowSortedKnowledgeAxioms.distribution.realize (stage GorbowAtomicRegistry.ground initial (k+1)) Fin.elim0 :=
  GorbowKnowledgeDispatchProof.positiveDistribution GorbowAtomicRegistry.ground
    GorbowAtomicRegistryProof.originalDispatch.1 GorbowAtomicRegistryProof.originalDispatch.2 initial k

theorem axiomThreshold : Comparators.GorbowNonreflectiveFragment.AxiomThreshold := by
  intro σ h initial k hk
  cases k with
  | zero => omega
  | succ k =>
    have ho := GorbowAtomicTruthProof.otherCodedClauses initial k
    have hf := GorbowKnowledgeDispatchProof.fixedClauses GorbowAtomicRegistry.ground
      (extensions GorbowAtomicRegistry.ground initial (k+1))
    cases h with
    | negation => exact ho.1
    | implication => exact ho.2.1
    | conjunction => exact ho.2.2.1
    | disjunction => exact ho.2.2.2.1
    | universal => exact ho.2.2.2.2.1
    | existential => exact ho.2.2.2.2.2.1
    | barcan => exact ho.2.2.2.2.2.2
    | atomic R names ha hi hc => exact GorbowAtomicTruthProof.atomicSchemas _ _ R names ha hi hc initial k
    | nontriviality => exact hf.1
    | bridge => exact hf.2.1
    | veracity => exact hf.2.2
    | distribution => exact knowledgePositive initial k

theorem finiteBlockThreshold : Comparators.GorbowNonreflectiveFragment.FiniteBlockThreshold := by
  intro initial used N σ p h k hk
  apply GorbowTheoryProofProof.theorySoundness _ 0 σ p (stage GorbowAtomicRegistry.ground initial k) _ Fin.elim0
  intro τ ht
  rcases ht with ha | hm
  · exact axiomThreshold τ ha initial k (le_trans (le_max_left 1 N) hk)
  · exact h τ hm k (le_trans (le_max_right 1 N) hk)

theorem indexedSoundness : Comparators.GorbowNonreflectiveFragment.IndexedSoundness := by
  intro N σ p
  induction p with
  | «axiom» h => exact axiomThreshold _ h
  | core p => intro initial; exact GorbowSortedRevisionEventualProof.coreThreshold _ initial _ p
  | mp p q hp hq =>
    intro initial
    exact GorbowSortedRevisionEventualProof.modusPonens _ initial _ _ _ _ (hp initial) (hq initial)
  | raise h p hp => intro initial k hk; exact hp initial k (le_trans h hk)
  | truthNec p hp => intro initial; exact (GorbowSortedRevisionEventualProof.ruleThresholds _ initial _ _).1 (hp initial)
  | truthConec p hp => intro initial; exact (GorbowSortedRevisionEventualProof.ruleThresholds _ initial _ _).2.1 (hp initial)
  | knowledgeNec p hp => intro initial; exact (GorbowSortedRevisionEventualProof.ruleThresholds _ initial _ _).2.2 (hp initial)
  | truthKnowledge p hp =>
    intro initial
    exact (GorbowSortedRevisionEventualProof.ruleThresholds _ initial _ _).2.2
      ((GorbowSortedRevisionEventualProof.ruleThresholds _ initial _ _).2.1 (hp initial))
  | block used p previous ih =>
    intro initial
    exact finiteBlockThreshold initial used _ _ p (fun τ ht => ih τ ht initial)

theorem concreteModel : Comparators.GorbowNonreflectiveFragment.ConcreteModel :=
  fun N σ p => indexedSoundness N σ p GorbowKnowledgeDispatch.emptyInitial N (le_refl N)

theorem finiteCommonStage : Comparators.GorbowNonreflectiveFragment.FiniteCommonStage := by
  intro sentences
  induction sentences with
  | nil => intro _; exact ⟨0,by simp⟩
  | cons σ rest ih =>
    intro h
    obtain ⟨N,⟨p⟩⟩ := h σ (by simp)
    obtain ⟨M,hM⟩ := ih (fun τ ht => h τ (by simp [ht]))
    refine ⟨max N M,?_⟩
    intro initial τ ht k hk
    rcases List.mem_cons.mp ht with rfl | ht
    · exact indexedSoundness N _ p initial k (le_trans (le_max_left N M) hk)
    · exact hM initial τ ht k (le_trans (le_max_right N M) hk)

theorem ruleClosure : Comparators.GorbowNonreflectiveFragment.RuleClosure := by
  intro σ
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨N,⟨p⟩⟩; exact ⟨N+1,⟨.truthNec p⟩⟩
  · rintro ⟨N,⟨p⟩⟩; exact ⟨N,⟨.truthConec p⟩⟩
  · rintro ⟨N,⟨p⟩⟩; exact ⟨N+1,⟨.knowledgeNec p⟩⟩
  · rintro ⟨N,⟨p⟩⟩; exact ⟨N+1,⟨.truthKnowledge p⟩⟩

theorem fragmentConsistency : Comparators.GorbowNonreflectiveFragment.FragmentConsistency := by
  rintro ⟨N,⟨p⟩⟩
  exact falseEquality_not_realized _ (concreteModel N falseEquality p)

theorem gorbowNonreflectiveFragment : Comparators.GorbowNonreflectiveFragment.Target :=
  ⟨axiomThreshold,finiteBlockThreshold,indexedSoundness,concreteModel,finiteCommonStage,ruleClosure,fragmentConsistency⟩
end LogicLineages.ComputabilityKnowledge.GorbowNonreflectiveFragmentProof
