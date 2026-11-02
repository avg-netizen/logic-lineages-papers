module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FiniteQueryPrimitivesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.TypeClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.HeadClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ComparisonFreeVariablesProof
public import LogicLineages.OrdinalComparison.SourceOpenedObservationsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FiniteQueryPrimitivesSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open RecursiveComparison ComparisonFreeVariables FiniteQueryPrimitives

theorem literalHeadCalibration : FiniteQueryPrimitivesTargets.LiteralHeadCalibration := by
  intro Symbol arity Γ τ q
  induction q using MarkedTerm.rec
    (motive_2 := fun Γ types args => ∀ P,argumentsAllowed P args ↔ ∀ h ∈ argumentHeads args,P h) with
  | var v => intro P; simp [headsAllowed,markedHeads]
  | lam body ih => exact ih
  | ordinary hd base ih => intro P; simp [headsAllowed,markedHeads,ih]
  | marked hd out base types extras ihb ihe =>
      intro P
      simp only [headsAllowed,markedHeads,List.mem_cons,List.mem_append,forall_eq_or_imp,ihb,ihe]
      constructor
      · intro h; exact ⟨h.1,fun q hq => hq.elim (h.2.1 q) (h.2.2 q)⟩
      · intro h; exact ⟨h.1,⟨fun q hq => h.2 q (Or.inl hq),fun q hq => h.2 q (Or.inr hq)⟩⟩
  | nil => simp [argumentsAllowed,argumentHeads]
  | cons q rest ihq ihr =>
      rename_i P
      simp only [argumentsAllowed,argumentHeads,ihq,ihr,List.mem_append]
      constructor
      · intro h v hv; exact hv.elim (h.1 v) (h.2 v)
      · intro h; exact ⟨fun v hv => h v (Or.inl hv),fun v hv => h v (Or.inr hv)⟩

theorem rootType {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty} {K : Ty → Prop}
    (q : MarkedTerm Symbol arity Γ τ) (h : typesAllowed K q) : K τ := by
  cases q <;> first | exact h | exact h.1

theorem argumentTypeMembership {Symbol : Type} {arity : Symbol → Nat} {Γ types : List Ty}
    (K : Ty → Prop) (args : Arguments Symbol arity Γ types) :
    argumentTypesAllowed K args ↔ ∀ p ∈ argumentList args,typesAllowed K p.2 := by
  induction types with
  | nil => cases args; simp [argumentTypesAllowed,argumentList]
  | cons σ types ih => cases args with
    | cons q rest => simp only [argumentTypesAllowed,argumentList,List.mem_cons,forall_eq_or_imp,ih]

theorem argumentHeadMembership {Symbol : Type} {arity : Symbol → Nat} {Γ types : List Ty}
    (P : Head Symbol → Prop) (args : Arguments Symbol arity Γ types) :
    argumentsAllowed P args ↔ ∀ p ∈ argumentList args,headsAllowed P p.2 := by
  induction types with
  | nil => cases args; simp [argumentsAllowed,argumentList]
  | cons σ types ih => cases args with
    | cons q rest => simp only [argumentsAllowed,argumentList,List.mem_cons,forall_eq_or_imp,ih]

theorem suffixTypes {K : Ty → Prop} (hc : SubtypeClosed K) (types : List Ty) (τ : Ty)
    (h : K (arrows types τ)) : (∀ υ ∈ types,K υ) ∧ K τ := by
  induction types with
  | nil => exact ⟨by simp,h⟩
  | cons σ rest ih =>
      have hd : K σ := hc _ h _ (by simp [arrows,Ty.subtypes,Ty.mem_subtypes_self])
      have ht : K (arrows rest τ) := hc _ h _ (by simp [arrows,Ty.subtypes,Ty.mem_subtypes_self])
      obtain ⟨hrest,hτ⟩ := ih ht
      exact ⟨fun υ hυ => (List.mem_cons.mp hυ).elim (fun he => he ▸ hd) (hrest υ),hτ⟩

theorem selfPayload {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    (K : Ty → Prop) (P : Head Symbol → Prop) (a : Allowed Γ)
    (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f))
    (extraTypes : List Ty) (extras : Arguments Symbol arity Γ extraTypes) (τ : Ty)
    (hK : typesAllowed K (.marked f τ base extraTypes extras))
    (hP : headsAllowed P (.marked f τ base extraTypes extras))
    (ha : Supported (.marked f τ base extraTypes extras) a)
    (requested : List Ty) (hr : ∀ υ ∈ requested,K υ) :
    argumentTypesAllowed K (selfArguments f base extraTypes extras requested) ∧
    argumentsAllowed P (selfArguments f base extraTypes extras requested) ∧
    ArgumentsSupported (selfArguments f base extraTypes extras requested) a := by
  induction requested with
  | nil => exact ⟨trivial,trivial,trivial⟩
  | cons υ rest ih =>
      obtain ⟨ht,hp,hs⟩ := ih (fun σ hσ => hr σ (List.mem_cons_of_mem υ hσ))
      exact ⟨⟨⟨hr υ List.mem_cons_self,hK.2⟩,ht⟩,⟨hP,hp⟩,⟨ha,hs⟩⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.FiniteQueryPrimitivesSupportProof
