module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceObservationCodingTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceObservationCodingProof
open Source Source.SourceTypedPorts Source.SourcePortContexts Source.SourceOpenedObservations SourceObservationCoding

theorem variableIndexInjective {Γ : List Ty} {τ : Ty} (v w : Variable Γ τ)
    (h : variableIndex v=variableIndex w) : v=w := by
  induction v with
  | here => cases w <;> simp_all [variableIndex]
  | there v ih =>
      cases w with
      | here => simp [variableIndex] at h
      | there w => exact congrArg Variable.there (ih w (Nat.succ.inj h))

theorem argumentCodesInjective {Symbol : Type} : Function.Injective (@argumentCodes Symbol) := by
  intro xs
  induction xs with
  | nil => intro ys h; cases ys <;> simp_all [argumentCodes]
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil => cases h
      | cons y ys =>
          have he := Code.argumentsCons.inj h
          exact congrArg₂ List.cons he.1 (ih he.2)

theorem termCodeInjective : SourceObservationCodingTargets.TermCodeInjective := by
  intro Symbol arity Γ τ t
  induction t with
  | var v =>
      intro u h
      cases u <;> simp only [termCode] at h <;> try contradiction
      rename_i w
      exact congrArg Term.var (variableIndexInjective v w (Code.var.inj h))
  | app f a ihf iha =>
      intro u h
      cases u <;> simp only [termCode] at h <;> try contradiction
      rename_i υ g b
      obtain ⟨he,hf,ha⟩ := Code.app.inj h
      cases he
      exact congrArg₂ Term.app (ihf hf) (iha ha)
  | lam body ih =>
      intro u h
      cases u <;> simp only [termCode] at h <;> try contradiction
      rename_i other
      exact congrArg Term.lam (ih (Code.lam.inj h).2)
  | zeroC => intro u h; cases u <;> simp_all [termCode]
  | succC => intro u h; cases u <;> simp_all [termCode]
  | caseC υ => intro u h; cases u <;> simp_all [termCode]
  | recC υ => intro u h; cases u <;> simp_all [termCode]
  | ranked hd args ih =>
      intro u h
      cases u <;> simp only [termCode] at h <;> try contradiction
      rename_i hd' args'
      obtain ⟨hh,ha⟩ := Code.ranked.inj h
      subst hd'
      have hl := argumentCodesInjective ha
      apply congrArg (Term.ranked hd)
      funext i
      apply ih i
      exact congrFun (List.ofFn_inj.mp hl) i

theorem observationCodeInjective : SourceObservationCodingTargets.ObservationCodeInjective := by
  intro Symbol arity Γ B o p h
  rcases o with ⟨P,τ,t⟩
  rcases p with ⟨Q,υ,u⟩
  simp only [observationCode,Prod.mk.injEq] at h
  obtain ⟨hp,ht,hc⟩ := h
  subst Q
  subst υ
  have he := termCodeInjective Symbol arity _ _ hc
  subst u
  rfl

theorem termEqualCorrect : SourceObservationCodingTargets.TermEqualCorrect := by
  intro Symbol inst arity Γ τ s t
  simp only [termEqual,decide_eq_true_eq]
  exact ⟨fun h => termCodeInjective Symbol arity Γ τ h,congrArg termCode⟩

theorem observationEqualCorrect : SourceObservationCodingTargets.ObservationEqualCorrect := by
  intro Symbol inst arity Γ B o p
  simp only [observationEqual,decide_eq_true_eq]
  exact ⟨fun h => observationCodeInjective Symbol arity Γ B h,congrArg observationCode⟩

/-- Executable equality; no classical choice is used by its implementation. -/
def termDecidableEq {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty} :
    DecidableEq (Term Symbol arity Γ τ) := fun s t =>
  if h : termEqual s t=true then isTrue ((termEqualCorrect Symbol inferInstance arity Γ τ s t).mp h)
  else isFalse (fun he => h ((termEqualCorrect Symbol inferInstance arity Γ τ s t).mpr he))

/-- Equality of actual observations, including ports and dependent body type. -/
def observationDecidableEq {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Γ : List Ty} {B : Nat} :
    DecidableEq (Observation Symbol arity Γ B) := fun o p =>
  if h : observationEqual o p=true then isTrue ((observationEqualCorrect Symbol inferInstance arity Γ B o p).mp h)
  else isFalse (fun he => h ((observationEqualCorrect Symbol inferInstance arity Γ B o p).mpr he))

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceObservationCodingProof
