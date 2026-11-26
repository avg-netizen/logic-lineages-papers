module
public import LogicLineages.StandardControlCurrent.PolicyFiniteCounterexampleProof
public import LogicLineages.StandardControlCurrent.PolicyFiniteProgramsProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyFiniteProof
open OrdinalComparison Source Source.ForwardTranslation Source.SourceClasses Source.AdmissibleSum Source.OriginalDomain
open LevelTwoCounterexample
theorem counterexamples (p : Policy) (Γ : List Ty) (hΓ : ∀ σ ∈ Γ,σ=Ty.ground)
    (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ)
    (hla : PolicyFinite.FiniteSource p a) (hlb : PolicyFinite.FiniteSource p b) (mode : Nat) :
    ∃ (av : OrdinalVector Γ τ.level) (bv : OrdinalVector Γ υ.level) (pack : Pair.Package),
      AdmissibleAssignment.assignment p a=some av ∧ AdmissibleAssignment.assignment p b=some bv ∧
      PolicyFinite.admittedCompile p (Γ.length,mode,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)=some pack ∧
      LevelTwoDecisionCompletion.PackageCertified pack ∧
      (Pair.Closed pack ↔ ∃ s : AdmissibleSubstitution Γ, ¬PolicyLevelTwo.originalRelation mode av bv s) := by
  obtain ⟨av,bv,pack,ha,hb,hc,hcert,he⟩ := numeric_counterexamples p Γ hΓ τ υ a b hla hlb mode
  have hadmit := (typed_accepts p Γ hΓ τ υ a b mode).mpr ⟨hla,hlb⟩
  refine ⟨av,bv,pack,ha,hb,?_,hcert,?_⟩
  · simp only [PolicyFinite.admittedCompile,hadmit,if_true,hc]
  · rw [he]
    constructor
    · rintro ⟨ρ,hp,hbad⟩
      obtain ⟨s,hs⟩ := DefaultSourceDomainProof.domain.1 Γ hΓ ρ hp
      exact ⟨s,fun h => hbad ((PolicyLevelTwoProof.relation_domain mode av bv s ρ hs).mp h)⟩
    · rintro ⟨s,hbad⟩
      obtain ⟨ρ,hp,hs⟩ := DefaultSourceDomainProof.domain.2 Γ hΓ s
      exact ⟨ρ,hp,fun h => hbad ((PolicyLevelTwoProof.relation_domain mode av bv s ρ hs).mpr h)⟩


theorem exact_class : PolicyFiniteTargets.ExactClass := by
  intro p q
  refine ⟨raw_class p q,?_⟩
  cases hh : PolicyFinite.accepts p q with
  | false => simp [PolicyFinite.decision,PolicyFinite.admittedCompile,PolicyFinite.solve,hh]
  | true =>
    obtain ⟨τ,υ,a,b,ha,hb,hfa,hfb⟩ := (raw_class p q).mp hh
    obtain ⟨av,bv,pack,_,_,hc,_,_⟩ := numeric_counterexamples p (List.replicate q.1 Ty.ground)
      (fun _ hs => List.eq_of_mem_replicate hs) τ υ a b hfa hfb q.2.1
    have hc' : PolicyLevelTwo.compile p q=some pack := by
      simpa only [List.length_replicate,ha,hb] using hc
    simp [PolicyFinite.decision,PolicyFinite.admittedCompile,hh,hc']
theorem typed : PolicyFiniteTargets.TypedDecision := by
  classical
  intro policy Γ hΓ τ υ a b hla hlb mode
  obtain ⟨av,bv,pack,ha,hb,hc,hcert,he⟩ := counterexamples policy Γ hΓ τ υ a b hla hlb mode
  let q : SourceCode.Input := (Γ.length,mode,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)
  have hpackage := LevelTwoDecisionCompletion.DecisionProof.actualPackageDecision pack hcert
  have hd : PolicyFinite.decision policy q=some (!LevelTwoDecisionCompletion.packageCounterexample pack) := by
    simp only [PolicyFinite.decision,q,hc,Option.map_some]
  have hs : PolicyFinite.solve policy q=(!LevelTwoDecisionCompletion.packageCounterexample pack) := by
    simp only [PolicyFinite.solve,hd,Option.getD_some]
  refine ⟨av,bv,ha,hb,?_,?_⟩
  · change PolicyFinite.decision policy q=some (PolicyFinite.solve policy q)
    rw [hd,hs]
  · change PolicyFinite.solve policy q=true ↔ _
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

theorem full : PolicyFiniteTargets.Full := ⟨coefficient_check,programs,exact_class,typed,recursor_free⟩
end LogicLineages.StandardControlCurrent.PolicyFiniteProof
