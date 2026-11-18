module
public import LogicLineages.StandardControlCurrent.PolicyLevelTwoDomainProof
public import LogicLineages.StandardControlCurrent.PolicyLevelTwoProgramsProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyLevelTwoProof
open OrdinalComparison Source Source.ForwardTranslation Source.SourceClasses LevelTwoCounterexample

theorem typed : PolicyLevelTwoTargets.TypedDecision := by
  classical
  intro policy Γ hΓ τ υ a b hla hlb mode
  obtain ⟨av,bv,pack,ha,hb,hc,hcert,he⟩ := counterexamples policy Γ hΓ τ υ a b hla hlb mode
  let q : SourceCode.Input := (Γ.length,mode,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)
  have hpackage := LevelTwoDecisionCompletion.DecisionProof.actualPackageDecision pack hcert
  have hd : PolicyLevelTwo.decision policy q=some (!LevelTwoDecisionCompletion.packageCounterexample pack) := by
    simp only [PolicyLevelTwo.decision,hc,Option.map_some]
  have hs : PolicyLevelTwo.solve policy q=(!LevelTwoDecisionCompletion.packageCounterexample pack) := by
    simp only [PolicyLevelTwo.solve,hd,Option.getD_some]
  refine ⟨av,bv,ha,hb,?_,?_⟩
  · change PolicyLevelTwo.decision policy q=some (PolicyLevelTwo.solve policy q)
    rw [hd,hs]
  · change PolicyLevelTwo.solve policy q=true ↔ _
    rw [hs]
    constructor
    · intro h s
      by_contra hbad
      have ht := hpackage.mpr (he.mpr ⟨s,hbad⟩)
      simp only [ht,Bool.not_true,Bool.false_eq_true] at h
    · intro hall
      cases hh : LevelTwoDecisionCompletion.packageCounterexample pack with
      | false => rfl
      | true =>
        obtain ⟨s,hbad⟩ := he.mp (hpackage.mp hh)
        exact False.elim (hbad (hall s))

theorem full : PolicyLevelTwoTargets.Full := ⟨programs,exact_domain,counterexamples,typed⟩
end LogicLineages.StandardControlCurrent.PolicyLevelTwoProof
