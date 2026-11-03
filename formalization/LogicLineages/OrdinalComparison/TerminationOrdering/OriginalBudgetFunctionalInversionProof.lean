module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalDerivationBudgetProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceFinalTransitivitySupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalBudgetFunctionalInversionProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication RecursiveComparison SourceSharpeningInversionProof

theorem ordinaryFrame {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (n : Nat) (s t : Packed Symbol arity Gamma)
    (h : OriginalDerivationBudget.Weak Symbol arity above (n+1) Gamma s t) :
    ∀ (f g : Head Symbol) (ss : Arguments Symbol arity Gamma (headArguments arity f))
      (ts : Arguments Symbol arity Gamma (headArguments arity g)),
    s=⟨headResult f,.ordinary f ss⟩ → t=⟨headResult g,.ordinary g ts⟩ →
      (headEquivalent f g ∧ ∃ matched,(argumentList ts).Perm matched ∧
        WeakMatch Symbol arity above Gamma (argumentList ss) matched) ∨
      OriginalDerivationBudget.Weak Symbol arity above n Gamma ⟨_,.marked f (headResult f) ss [] .nil⟩ t ∨
      OriginalDerivationBudget.Weak Symbol arity above n Gamma s t := by
  cases h
  case fun_ f0 g0 baseS baseT matched he heType hp hm =>
    intro f g ss ts hs ht
    have hf : f0=f := Option.some.inj (congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) hs)
    have hg : g0=g := Option.some.inj (congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) ht)
    cases hf
    cases hg
    cases hs
    cases ht
    exact .inl ⟨by assumption,_,by assumption,OriginalDerivationBudgetErasureProof.matchSound (by assumption)⟩
  case put f0 base target hw =>
    intro f g ss ts hs ht
    have hf : f0=f := Option.some.inj (congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) hs)
    cases hf
    have hb : MarkedTerm.ordinary f0 base=MarkedTerm.ordinary f0 ss := by injection hs
    cases hb
    exact .inr (.inl (ht ▸ hw))
  case up => intros; exact .inr (.inr (by assumption))
  all_goals
    intro f g ss ts hs ht
    have hn := congrArg rootShape hs
    cases hn

theorem markedGroundFrame {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (n : Nat) (s t : Packed Symbol arity Gamma)
    (h : OriginalDerivationBudget.Weak Symbol arity above (n+1) Gamma s t) :
    ∀ (f : Head Symbol) (ss : Arguments Symbol arity Gamma (headArguments arity f))
      (g : Symbol) (ts : Arguments Symbol arity Gamma (List.replicate (arity g) .ground)),
    s=⟨.ground,.marked f .ground ss [] .nil⟩ → t=⟨.ground,.ordinary (.ranked g) ts⟩ →
      headAbove above f (.ranked g) ∨
      (headEquivalent f (.ranked g) ∧ StrictMultiset Symbol arity above Gamma (argumentList ss) (argumentList ts)) ∨
      (∃ (sigma : Ty) (selected : MarkedTerm Symbol arity Gamma sigma) (types : List Ty) (suffix : sigma=arrows types .ground)
        (result : MarkedTerm Symbol arity Gamma .ground),
        (⟨sigma,selected⟩ : Packed Symbol arity Gamma)∈argumentList ss ∧
        applyOriginalWith selected (fun v => .var v) (selfArguments f ss [] .nil types) suffix=some result ∧
        OriginalDerivationBudget.Weak Symbol arity above n Gamma ⟨.ground,result⟩ t) ∨
      OriginalDerivationBudget.Weak Symbol arity above n Gamma s t := by
  cases h
  case select f0 extraTypes requested suffix base extras selected result target hm ha hw =>
    intro f ss g ts hs ht
    have hf : f0=f := Option.some.inj (congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) hs)
    cases hf
    have hType := congrArg Sigma.fst hs
    cases hType
    have hb : MarkedTerm.marked f0 .ground base extraTypes extras=MarkedTerm.marked f0 .ground ss [] .nil := by injection hs
    cases hb
    simp only [argumentList,List.append_nil] at hm
    exact .inr (.inr (.inl ⟨_,selected,requested,suffix,result,hm,ha,ht ▸ hw⟩))
  case copy f0 g0 base extraTypes extras targetBase hp hw =>
    intro f ss g ts hs ht
    have hf : f0=f := Option.some.inj (congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) hs)
    have hg : g0=.ranked g := Option.some.inj (congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) ht)
    cases hf
    cases hg
    exact .inl (by assumption)
  case stat f0 g0 base extraTypes extras targetBase he hm hw =>
    intro f ss g ts hs ht
    have hf : f0=f := Option.some.inj (congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) hs)
    have hg : g0=.ranked g := Option.some.inj (congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) ht)
    cases hf
    cases hg
    cases hs
    cases ht
    exact .inr (.inl ⟨by assumption,OriginalDerivationBudgetErasureProof.multisetSound (by assumption)⟩)
  case up => intros; exact .inr (.inr (.inr (by assumption)))
  case fAbs =>
    intro f ss g ts hs ht
    have hn := congrArg rootShape ht
    cases hn
  all_goals
    intro f ss g ts hs ht
    first
    | have hn := congrArg rootShape hs; cases hn
    | have hn := congrArg rootShape ht; cases hn

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalBudgetFunctionalInversionProof
