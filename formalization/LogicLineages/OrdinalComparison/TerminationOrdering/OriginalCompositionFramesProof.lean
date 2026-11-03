module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinarySyntaxCoverageProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalBudgetUnmarkingProof

@[expose] public section
/-! Internal constructor frames for the frozen ORIGINAL composition target.
The body postcomposition premise below is an explicit induction hypothesis;
this file does not claim that premise or full transitivity. -/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalCompositionFramesProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication RecursiveComparison
open SourceSharpeningInversionProof

theorem weakType {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {s t : Packed Symbol arity Gamma}
    (h : Weak Symbol arity above Gamma s t) : s.1=t.1 := by
  cases h
  case fun_ => assumption
  all_goals rfl

theorem putPacked {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (f : Head Symbol)
    (base : Arguments Symbol arity Gamma (headArguments arity f))
    (t : Packed Symbol arity Gamma)
    (h : Weak Symbol arity above Gamma ⟨_,.marked f (headResult f) base [] .nil⟩ t) :
    Weak Symbol arity above Gamma ⟨_,.ordinary f base⟩ t := by
  rcases t with ⟨tau,t⟩
  have ht : headResult f=tau := weakType above h
  cases ht
  exact .put f base t h

theorem selectPacked {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (f : Head Symbol)
    (base : Arguments Symbol arity Gamma (headArguments arity f))
    (extraTypes : List Ty) (extras : Arguments Symbol arity Gamma extraTypes)
    (sigma tau : Ty) (types : List Ty) (q : MarkedTerm Symbol arity Gamma sigma)
    (r : MarkedTerm Symbol arity Gamma tau) (suffix : sigma=arrows types tau)
    (hm : (⟨sigma,q⟩ : Packed Symbol arity Gamma)∈argumentList base++argumentList extras)
    (ha : applyOriginalWith q (fun v => .var v) (selfArguments f base extraTypes extras types) suffix=some r)
    (t : Packed Symbol arity Gamma)
    (h : Weak Symbol arity above Gamma ⟨tau,r⟩ t) :
    Weak Symbol arity above Gamma ⟨tau,.marked f tau base extraTypes extras⟩ t := by
  rcases t with ⟨upsilon,t⟩
  have ht : tau=upsilon := weakType above h
  cases ht
  exact .select f base extraTypes extras types q r t suffix hm ha h

theorem lambdaPostFrame {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {s t : Packed Symbol arity Gamma}
    (h : Weak Symbol arity above Gamma s t) :
    ∀ sigma tau (mid last : MarkedTerm Symbol arity (sigma::Gamma) tau),
      t=⟨.arrow sigma tau,.lam mid⟩ →
      (∀ p : Packed Symbol arity (sigma::Gamma),
        Weak Symbol arity above (sigma::Gamma) p ⟨tau,mid⟩ →
        Weak Symbol arity above (sigma::Gamma) p ⟨tau,last⟩) →
      Weak Symbol arity above Gamma s ⟨.arrow sigma tau,.lam last⟩ := by
  induction h using Weak.rec
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
  case abs a b hab ih =>
    intro sigma tau mid last he post
    obtain ⟨hdom,hcod⟩ := Ty.arrow.inj (congrArg Sigma.fst he)
    cases hdom
    cases hcod
    have ht : MarkedTerm.lam b=MarkedTerm.lam mid := by injection he
    have hb : b=mid := by injection ht
    subst b
    exact .abs a last (post _ hab)
  case put f base target hw ih =>
    intro sigma tau mid last he post
    exact putPacked above f base _ (ih sigma tau mid last he post)
  case select f base extraTypes extras types q r target suffix hm ha hw ih =>
    intro sigma tau mid last he post
    exact selectPacked above f base extraTypes extras _ _ types q r suffix hm ha _
      (ih sigma tau mid last he post)
  case fAbs f base extraTypes extras target hw ih =>
    intro sigma tau mid last he post
    obtain ⟨hdom,hcod⟩ := Ty.arrow.inj (congrArg Sigma.fst he)
    cases hdom
    cases hcod
    have ht : MarkedTerm.lam target=MarkedTerm.lam mid := by injection he
    have hb : target=mid := by injection ht
    subst target
    exact .fAbs f base extraTypes extras last (post _ hw)
  case var v =>
    intro sigma tau mid last he post
    have hn := congrArg rootShape he
    cases hn
  case fun_ =>
    intros
    have hn := congrArg rootShape (by assumption)
    cases hn
  case copy =>
    intros
    have hn := congrArg rootShape (by assumption)
    cases hn
  case stat =>
    intros
    have hn := congrArg rootShape (by assumption)
    cases hn
  all_goals intros; trivial

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalCompositionFramesProof
