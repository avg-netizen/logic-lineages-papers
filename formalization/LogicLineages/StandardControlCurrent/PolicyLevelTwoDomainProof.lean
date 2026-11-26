module
public import LogicLineages.StandardControlCurrent.PolicyLevelTwoCounterexampleProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyLevelTwoProof
open OrdinalComparison Source Source.ForwardTranslation Source.SourceClasses Source.AdmissibleSum Source.OriginalDomain
open LevelTwoCounterexample
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

private theorem vector_calibration {Γ : List Ty} {n : Nat} (v : OrdinalVector Γ n)
    (s : AdmissibleSubstitution Γ) (ρ : OrdinalComponent Γ → Nat)
    (hρ : ∀ c, valuation s c=(ρ c : Ordinal)) (j : Nat) :
    PolicySourceEquality.vectorAt v s j=sourceVectorAtValue v ρ j := by
  have he : valuation s = fun c => (ρ c : Ordinal) := funext hρ
  simp only [PolicySourceEquality.vectorAt,sourceVectorAtValue,ordinalVectorAt]
  split <;> simp only [expressionValue,he,denote]

theorem relation_domain {Γ : List Ty} {n m : Nat} (mode : Nat)
    (a : OrdinalVector Γ n) (b : OrdinalVector Γ m)
    (s : AdmissibleSubstitution Γ) (ρ : OrdinalComponent Γ → Nat)
    (hρ : ∀ c, valuation s c=(ρ c : Ordinal)) :
    PolicyLevelTwo.originalRelation mode a b s ↔ SourceCode.sourceRelation mode a b ρ := by
  unfold PolicyLevelTwo.originalRelation SourceCode.sourceRelation
  by_cases h0 : mode=0
  · simp only [h0,if_true,vector_calibration _ s ρ hρ,SourceComparisonAt,Bool.false_eq_true,if_false]
    constructor
    · intro h; exact ⟨fun j => h (j+1),h 0⟩
    · rintro ⟨hp,hz⟩ j
      cases j with
      | zero => exact hz
      | succ j => exact hp j
  · by_cases h1 : mode=1
    · simp only [h0,h1,if_false,if_true,vector_calibration _ s ρ hρ,SourceComparisonAt]
      exact and_comm
    · simp only [h0,h1,if_false,vector_calibration _ s ρ hρ]

theorem counterexamples : PolicyLevelTwoTargets.Counterexamples := by
  intro p Γ hΓ τ υ a b hla hlb mode
  obtain ⟨av,bv,pack,ha,hb,hc,hcert,he⟩ := numeric_counterexamples p Γ hΓ τ υ a b hla hlb mode
  have hadmit := LevelTwoDecisionCompletion.DecisionProof.typed_accepts Γ hΓ τ υ a b hla hlb mode
  refine ⟨av,bv,pack,ha,hb,?_,hcert,?_⟩
  · simp only [PolicyLevelTwo.admittedCompile,hadmit,if_true,hc]
  · rw [he]
    constructor
    · rintro ⟨ρ,hp,hbad⟩
      obtain ⟨s,hs⟩ := DefaultSourceDomainProof.domain.1 Γ hΓ ρ hp
      exact ⟨s,fun h => hbad ((relation_domain mode av bv s ρ hs).mp h)⟩
    · rintro ⟨s,hbad⟩
      obtain ⟨ρ,hp,hs⟩ := DefaultSourceDomainProof.domain.2 Γ hΓ s
      exact ⟨ρ,hp,fun h => hbad ((relation_domain mode av bv s ρ hs).mpr h)⟩

theorem exact_domain : PolicyLevelTwoTargets.ExactDomain := by
  intro p q
  cases hh : Admission.accepts q with
  | false => simp [PolicyLevelTwo.decision,PolicyLevelTwo.admittedCompile,PolicyLevelTwo.solve,hh]
  | true =>
    obtain ⟨τ,υ,a,b,ha,hb,hla,hlb⟩ := (AdmissionProof.exactGroundClass q).mp hh
    obtain ⟨av,bv,pack,_,_,hc,_,_⟩ := numeric_counterexamples p (List.replicate q.1 Ty.ground)
      (fun _ hs => List.eq_of_mem_replicate hs) τ υ a b hla hlb q.2.1
    have hc' : PolicyLevelTwo.compile p q=some pack := by
      simpa only [List.length_replicate,ha,hb] using hc
    simp [PolicyLevelTwo.decision,PolicyLevelTwo.admittedCompile,hh,hc']
end LogicLineages.StandardControlCurrent.PolicyLevelTwoProof
