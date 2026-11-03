module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceFinalTransitivitySupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.MarkedSourceCounterexampleInversionProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication RecursiveComparison SourceSharpeningInversionProof

theorem groundMemberType {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (n : Nat) (args : Arguments Symbol arity Gamma (List.replicate n .ground))
    (p : Packed Symbol arity Gamma) (hp : p∈argumentList args) : p.1=.ground := by
  induction n with
  | zero => cases args; cases hp
  | succ n ih =>
    cases args with
    | cons q rest =>
      rcases List.mem_cons.mp hp with he | hm
      · subst p; rfl
      · exact ih rest hm

theorem ordinaryInversion {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (s t : Packed Symbol arity Gamma) (h : Weak Symbol arity above Gamma s t) :
    ∀ (f : Symbol) (ss : Arguments Symbol arity Gamma (List.replicate (arity f) .ground))
      (g : Symbol) (ts : Arguments Symbol arity Gamma (List.replicate (arity g) .ground)),
    s=⟨.ground,.ordinary (.ranked f) ss⟩ → t=⟨.ground,.ordinary (.ranked g) ts⟩ →
      headEquivalent (.ranked f) (.ranked g) ∨
      Weak Symbol arity above Gamma ⟨.ground,.marked (.ranked f) .ground ss [] .nil⟩ ⟨.ground,.ordinary (.ranked g) ts⟩ := by
  cases h
  case fun_ f0 g0 baseS baseT matched he heType hp hm =>
    intro f ss g ts hs ht
    have hf : f0=.ranked f := Option.some.inj (congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) hs)
    have hg : g0=.ranked g := Option.some.inj (congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) ht)
    cases hf
    cases hg
    exact .inl (by assumption)
  case put f0 base target hw =>
    intro f ss g ts hs ht
    have hf : f0=.ranked f := Option.some.inj (congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) hs)
    cases hf
    have hb : MarkedTerm.ordinary (.ranked f) base=MarkedTerm.ordinary (.ranked f) ss := by injection hs
    cases hb
    exact .inr (ht ▸ hw)
  all_goals
    intro f ss g ts hs ht
    have hn := congrArg rootShape hs
    cases hn

theorem markedInversion {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (s t : Packed Symbol arity Gamma) (h : Weak Symbol arity above Gamma s t) :
    ∀ (f : Symbol) (ss : Arguments Symbol arity Gamma (List.replicate (arity f) .ground))
      (g : Symbol) (ts : Arguments Symbol arity Gamma (List.replicate (arity g) .ground)),
    s=⟨.ground,.marked (.ranked f) .ground ss [] .nil⟩ → t=⟨.ground,.ordinary (.ranked g) ts⟩ →
      headAbove above (.ranked f) (.ranked g) ∨
      (headEquivalent (.ranked f) (.ranked g) ∧ StrictMultiset Symbol arity above Gamma (argumentList ss) (argumentList ts)) ∨
      ∃ p∈argumentList ss,Weak Symbol arity above Gamma p ⟨.ground,.ordinary (.ranked g) ts⟩ := by
  cases h
  case select f0 extraTypes requested suffix base extras selected result target hm ha hw =>
    intro f ss g ts hs ht
    have hf : f0=.ranked f := Option.some.inj (congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) hs)
    cases hf
    have hType := congrArg Sigma.fst hs
    cases hType
    have hb : MarkedTerm.marked (.ranked f) .ground base extraTypes extras=MarkedTerm.marked (.ranked f) .ground ss [] .nil := by injection hs
    cases hb
    simp only [argumentList,List.append_nil] at hm
    have hSelected := groundMemberType (arity f) ss ⟨_,selected⟩ hm
    cases hSelected
    cases requested with
    | nil =>
      have hr : selected=result := Option.some.inj ((SourceSpecialApplicationProof.emptySpecialApplication Symbol arity Gamma .ground selected).symm.trans ha)
      subst result
      exact .inr (.inr ⟨⟨.ground,selected⟩,hm,ht ▸ hw⟩)
    | cons rho rest => cases suffix
  case fAbs f0 base types extras target hw =>
    intro f ss g ts hs ht
    have hn := congrArg rootShape ht
    cases hn
  case copy f0 g0 base extraTypes extras targetBase hp hw =>
    intro f ss g ts hs ht
    have hf : f0=.ranked f := Option.some.inj (congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) hs)
    have hg : g0=.ranked g := Option.some.inj (congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) ht)
    cases hf
    cases hg
    exact .inl (by assumption)
  case stat f0 g0 base extraTypes extras targetBase he hm hw =>
    intro f ss g ts hs ht
    have hf : f0=.ranked f := Option.some.inj (congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) hs)
    have hg : g0=.ranked g := Option.some.inj (congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) ht)
    cases hf
    cases hg
    cases hs
    cases ht
    exact .inr (.inl ⟨by assumption,by assumption⟩)
  all_goals
    intro f ss g ts hs ht
    have hn := congrArg rootShape hs
    cases hn

end LogicLineages.OrdinalComparison.TerminationOrdering.MarkedSourceCounterexampleInversionProof
