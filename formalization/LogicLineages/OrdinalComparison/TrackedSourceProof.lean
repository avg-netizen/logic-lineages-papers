module
public import LogicLineages.OrdinalComparison.TrackedSourceTargets
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentStatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.TrackedSource.Proof
open SourceFreeOccurrences AdmissibleAssignment

theorem erase_generated {k Γ F n} (e : Expr k Γ F n) : @Generated k Γ F n (erase e) := by
  induction e with
  | tracked => exact Generated.tracked
  | ground x => exact Generated.ground x
  | free t hf => exact Generated.free t hf
  | app f a ihf iha => exact Generated.app ihf iha
  | lam body ih => exact Generated.lam ih

theorem exactGrammar : Targets.ExactGrammar := by
  intro k Γ F n t
  constructor
  · intro ht
    induction ht with
    | tracked => exact ⟨.tracked,rfl⟩
    | ground x => exact ⟨.ground x,rfl⟩
    | free t hf => exact ⟨.free t hf,rfl⟩
    | app hf ha ihf iha =>
      obtain ⟨f,hf⟩ := ihf
      obtain ⟨a,ha⟩ := iha
      exact ⟨.app f a,by simp only [erase,hf,ha]⟩
    | lam hb ih =>
      obtain ⟨body,hb⟩ := ih
      exact ⟨.lam body,by simp only [erase,hb]⟩
  · rintro ⟨e,rfl⟩
    exact erase_generated e

theorem exactOccurrences : Targets.ExactOccurrences := by
  intro k Γ F n e
  induction e with
  | tracked | ground _ | free _ _ => rfl
  | app f a ihf iha => exact congrArg₂ List.append ihf iha
  | lam body ih => simp only [erase,freeOccurrences,occurrences,ih]

theorem mem_dropBound {Γ : List Ty} {σ τ : Ty} (x : Variable Γ σ)
    (xs : List (PackedVariable (τ :: Γ))) :
    (⟨σ,x⟩ : PackedVariable Γ)∈xs.filterMap dropBound ↔
      (⟨σ,Variable.there x⟩ : PackedVariable (τ :: Γ))∈xs := by
  constructor
  · intro h
    obtain ⟨⟨ρ,v⟩,hv,he⟩ := List.mem_filterMap.mp h
    cases v with
    | here => cases he
    | there v =>
      have he' : (⟨ρ,v⟩ : PackedVariable Γ)=⟨σ,x⟩ := Option.some.inj he
      cases he'
      exact hv
  · intro h
    exact List.mem_filterMap.mpr ⟨⟨σ,Variable.there x⟩,h,rfl⟩

theorem activity_occurrences {k Γ F n} (e : Expr k Γ F n) :
    active e=true ↔ (⟨Ty.curriedGround (k+1),F⟩ : PackedVariable Γ)∈occurrences e := by
  induction e with
  | tracked => simp only [active,occurrences,List.mem_singleton]
  | ground x =>
    simp only [active,occurrences,Bool.false_eq_true,false_iff,List.mem_singleton]
    intro he
    have ht := congrArg Sigma.fst he
    simp only [Ty.curriedGround] at ht
    cases ht
  | free t hf =>
    simp only [active,occurrences,Bool.false_eq_true,false_iff]
    exact hf
  | app f a ihf iha => simp only [active,occurrences,Bool.or_eq_true,List.mem_append,ihf,iha]
  | lam body ih =>
    simpa only [active,occurrences,mem_dropBound] using ih

theorem exactActivity : Targets.ExactActivity := by
  intro k Γ F n e
  rw [exactOccurrences k Γ F n e]
  exact activity_occurrences e

theorem actualAssignment : Targets.ActualAssignment := by
  intro k Γ F n e
  exact actualAdmissibleAssignmentGenerated Γ (Ty.curriedGround n) OrdinalSyntax.defaultPolicy (erase e)
end LogicLineages.OrdinalComparison.Source.TrackedSource.Proof
