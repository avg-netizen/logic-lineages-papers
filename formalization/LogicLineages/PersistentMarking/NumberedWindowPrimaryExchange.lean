import LogicLineages.PersistentMarking.NumberedWindowPrimary
import LogicLineages.PersistentMarking.NumberedWindowTypingBitsTargets

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryExchange
open NumberedWindowSyntax NumberedWindowDomain

/-- The two original rooted exchanges require actual admitted heads and
the manuscript's class-rank equivalence, not literal head equality. -/
def AllowedHeadPair (S : Spine.Signature) (K : List Ty) (f g : Head) : Prop :=
  HeadInWindow S K f ∧ HeadInWindow S K g ∧ Spine.Equivalent S f g

/- One occurrence of an actual primary root exchange in a congruence
context. The skeleton and the window typing guard are independent of the
executable check. This is equivalence, not an extra raw rule: both positions
of the separate auxiliary application admit contextual exchange. -/
mutual
inductive ExchangeShape (S : Spine.Signature) (K : List Ty) : NTerm → NTerm → Prop where
  | ordinary :
      AllowedHeadPair S K f g → f.result = g.result → bs.toList.Perm cs.toList →
      ExchangeShape S K (.ordinary f bs) (.ordinary g cs)
  | numbered :
      AllowedHeadPair S K f g → bs.toList.Perm cs.toList →
      ExchangeShape S K (.numbered f τ k bs es) (.numbered g τ k cs es)
  | lam : ExchangeShape S K Q R → ExchangeShape S K (.lam σ Q) (.lam σ R)
  | ordinaryBase :
      ArgsExchangeShape S K bs cs → ExchangeShape S K (.ordinary f bs) (.ordinary f cs)
  | numberedBase :
      ArgsExchangeShape S K bs cs →
      ExchangeShape S K (.numbered f τ k bs es) (.numbered f τ k cs es)
  | numberedExtra :
      ArgsExchangeShape S K es ds →
      ExchangeShape S K (.numbered f τ k bs es) (.numbered f τ k bs ds)
  | applicationFunction :
      ExchangeShape S K Q R → ExchangeShape S K (.auxApp σ τ Q A) (.auxApp σ τ R A)
  | applicationArgument :
      ExchangeShape S K A B → ExchangeShape S K (.auxApp σ τ Q A) (.auxApp σ τ Q B)

inductive ArgsExchangeShape (S : Spine.Signature) (K : List Ty) : NArgs → NArgs → Prop where
  | first : ExchangeShape S K Q R → ArgsExchangeShape S K (.cons Q as) (.cons R as)
  | later : ArgsExchangeShape S K as bs → ArgsExchangeShape S K (.cons Q as) (.cons Q bs)
end

/-- Both vertices inhabit exactly the same original typed numerical
universe. An elementary exchange may be identity at its rooted site,
since the original congruence allows a reflexive permutation/exchange. -/
def WindowExchange (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext) (τ : Ty)
    (Q R : NTerm) : Prop :=
  ExchangeShape S K Q R ∧ InWindow S K C τ Q ∧ InWindow S K C τ R

end LogicLineages.PersistentMarking.NumberedWindowPrimaryExchange
