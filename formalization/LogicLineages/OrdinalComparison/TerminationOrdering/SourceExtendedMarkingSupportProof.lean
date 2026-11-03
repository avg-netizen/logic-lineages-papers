module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedMarkingTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedMarkingSupportProof
open Source Source.SourceMarkedSyntax RecursiveComparison SourceExtendedMarking SourceSharpeningInversionProof

theorem alignment : SourceExtendedMarkingTargets.ActualMarkAlignment := by
  intro Symbol arity Gamma tau s
  induction s using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v =>
    constructor
    · intro r h; cases h
    · intro h; rfl
  | lam body ih =>
    constructor
    · intro r h
      cases hm : strictMark body with
      | none => simp only [strictMark,hm,Option.map_none] at h; cases h
      | some out =>
        simp only [strictMark,hm,Option.map_some] at h
        have he : MarkedTerm.lam out=r := Option.some.inj h
        subst r
        exact congrArg MarkedTerm.lam (ih.1 out hm)
    · intro h
      cases hm : strictMark body with
      | none => exact congrArg MarkedTerm.lam (ih.2 hm)
      | some out => simp only [strictMark,hm,Option.map_some] at h; cases h
  | ordinary f base ih => exact ⟨fun r h => Option.some.inj h,fun h => nomatch h⟩
  | marked f output base types extras ihb ihe =>
    constructor
    · intro r h; cases h
    · intro h; rfl
  | nil => trivial
  | cons q rest ihq ihr => trivial

theorem lambdaSource {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (s t : Packed Symbol arity Gamma)
    (h : SourceExtendedComparison.Weak Symbol arity above Gamma s t) :
    ∀ sigma tau (body : MarkedTerm Symbol arity (sigma::Gamma) tau),s=⟨.arrow sigma tau,.lam body⟩ →
      ∃ target : MarkedTerm Symbol arity (sigma::Gamma) tau,
        t=⟨.arrow sigma tau,.lam target⟩ ∧ SourceExtendedComparison.Weak Symbol arity above (sigma::Gamma) ⟨tau,body⟩ ⟨tau,target⟩ := by
  cases h <;> intro sigma tau body he <;> try { have hn := congrArg rootShape he; cases hn }
  case abs a b hb =>
    obtain ⟨hdom,hcod⟩ := Ty.arrow.inj (congrArg Sigma.fst he)
    cases hdom
    cases hcod
    have ht : MarkedTerm.lam a=MarkedTerm.lam body := by injection he
    have ha : a=body := by injection ht
    subst a
    exact ⟨b,rfl,hb⟩

theorem leftUnmark {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (above : Symbol → Symbol → Prop) (s : MarkedTerm Symbol arity Gamma tau) :
    ∀ t : MarkedTerm Symbol arity Gamma tau,SourceExtendedComparison.Weak Symbol arity above Gamma ⟨tau,star s⟩ ⟨tau,t⟩ →
      SourceExtendedComparison.Weak Symbol arity above Gamma ⟨tau,s⟩ ⟨tau,t⟩ := by
  induction s using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v => intro t h; exact h
  | @lam Gamma sigma tau body ih =>
    intro t h
    obtain ⟨b,ht,hb⟩ := lambdaSource above _ _ h sigma tau (star body) rfl
    have ht' : t=MarkedTerm.lam b := by injection ht
    subst t
    exact .abs body b (ih b hb)
  | ordinary f base ih => intro t h; exact .put f base t h
  | marked f output base types extras ihb ihe => intro t h; exact h
  | nil => trivial
  | cons q rest ihq ihr => trivial

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedMarkingSupportProof
