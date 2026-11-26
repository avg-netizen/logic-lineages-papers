module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimaryExchangeShapeProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeReflectProof
open NumberedWindowSyntax NumberedWindowPrimaryExchange NumberedWindowPrimaryExchangeBits
open NumberedWindowPrimaryExchangeHeadProof NumberedWindowPrimaryExchangeShapeProof

abbrev TermGoal (S : Spine.Signature) (K : List Ty) (Q : NTerm) : Prop :=
  ∀ R, exchangeBit S K Q R = true ↔ ExchangeShape S K Q R

abbrev ArgsGoal (S : Spine.Signature) (K : List Ty) (qs : NArgs) : Prop :=
  ∀ rs, argsExchangeBit S K qs rs = true ↔ ArgsExchangeShape S K qs rs

private theorem disagree {S K Q R} (e : exchangeBit S K Q R = false)
    (h : ¬ ExchangeShape S K Q R) : exchangeBit S K Q R = true ↔ ExchangeShape S K Q R := by
  simp only [e,Bool.false_eq_true,false_iff]
  exact h

private theorem disagreeArgs {S K qs rs} (e : argsExchangeBit S K qs rs = false)
    (h : ¬ ArgsExchangeShape S K qs rs) : argsExchangeBit S K qs rs = true ↔ ArgsExchangeShape S K qs rs := by
  simp only [e,Bool.false_eq_true,false_iff]
  exact h

private theorem nilCase (S : Spine.Signature) (K : List Ty) : ArgsGoal S K .nil := by
  intro rs
  cases rs <;> exact disagreeArgs rfl (by intro h; cases h)

private theorem consCase {S K Q qs} (iq : TermGoal S K Q) (ia : ArgsGoal S K qs) :
    ArgsGoal S K (.cons Q qs) := by
  intro rs
  cases rs with
  | nil => exact disagreeArgs rfl (by intro h; cases h)
  | cons R rs =>
    simp only [argsExchangeBit,Bool.or_eq_true,Bool.and_eq_true,iq R,ia rs,
      termIdentity,argsIdentity,consShape]

theorem term (S : Spine.Signature) (K : List Ty) (Q : NTerm) : TermGoal S K Q := by
  induction Q using NTerm.rec (motive_2 := ArgsGoal S K) with
  | free σ x =>
    intro R
    cases R <;> exact disagree rfl (by intro h; cases h)
  | bound σ i =>
    intro R
    cases R <;> exact disagree rfl (by intro h; cases h)
  | bottom σ =>
    intro R
    cases R <;> exact disagree rfl (by intro h; cases h)
  | lam σ Q ih =>
    intro R
    cases R <;> first
      | exact disagree rfl (by intro h; cases h)
      | simp only [exchangeBit,Bool.and_eq_true,decide_eq_true_eq,ih,lambdaShape]
  | ordinary f bs ih =>
    intro R
    cases R <;> first
      | exact disagree rfl (by intro h; cases h)
      | simp only [exchangeBit,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,
          headPair,permutation,ih,ordinaryShape]
  | numbered f τ k bs es ib ie =>
    intro R
    cases R <;> first
      | exact disagree rfl (by intro h; cases h)
      | simp only [exchangeBit,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,
          headPair,permutation,argsIdentity,ib,ie,numberedShape]
  | auxApp σ τ Q A iq ia =>
    intro R
    cases R <;> first
      | exact disagree rfl (by intro h; cases h)
      | simp only [exchangeBit,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,
          termIdentity,iq,ia,auxShape]
  | nil => first | exact nilCase S K | exact nilCase S K _
  | cons Q qs iq ia => first | exact consCase iq ia | exact consCase iq ia _

theorem args (S : Spine.Signature) (K : List Ty) (qs : NArgs) : ArgsGoal S K qs := by
  cases qs with
  | nil => exact nilCase S K
  | cons Q qs => exact consCase (term S K Q) (args S K qs)
termination_by structural qs

end LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeReflectProof
