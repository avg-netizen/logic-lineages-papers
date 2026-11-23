module

public import LogicLineages.NativeModule.PersistentMarking.Refinement
public import LogicLineages.NativeModule.PersistentMarking.ExtendedComparison

@[expose] public section

namespace LogicLineages.PersistentMarking.AuxiliaryTargets
open Spine

def RefinementReflexive : Prop := ∀ S q σ, PaperTerm S q σ → Refines S q q

def RefinementRetyping : Prop := ∀ S f τ ρ qb qe sb se,
  Refines S (.marked f τ qb qe) (.marked f τ sb se) →
  Refines S (.marked f ρ qb qe) (.marked f ρ sb se)

def RefinementMarkReflection : Prop := ∀ S q s r,
  Refines S q s → mark s = some r → ∃ p, mark q = some p ∧ Refines S p r

def OriginalWeakEmbedding : Prop := ∀ S q t, Weak S q t → ExtendedWeak S q t

def OriginalStrictEmbedding : Prop := ∀ S q t, Strict S q t → ExtendedStrict S q t

def ExtendedReflexive : Prop := ∀ S q σ, PaperTerm S q σ → ExtendedWeak S q q

/-- The marked strict auxiliary relation is explicitly not asserted well-founded. -/
def MarkedStrictSelf : Prop := ∀ S f τ base extras,
  PaperTerm S (.marked f τ base extras) τ →
  ExtendedStrict S (.marked f τ base extras) (.marked f τ base extras)

/-- Central endpoint frozen without a composition or elimination oracle.
Sources and intermediates may contain arbitrary marks. -/
def OrdinaryFinalCut : Prop := ∀ S s t u,
  ExtendedWeak S s t → ExtendedWeak S t u → Ordinary u → Weak S s u

/-- The literal two-stage escape alternative, not application associativity. -/
def PrefixEscape : Prop := ∀ S f ρ base extras domains₁ domains₂ τ q as bs r w,
  PaperTerm S (.marked f ρ base extras) ρ →
  PaperTerm S q (ArrowPrefix domains₁ (ArrowPrefix domains₂ τ)) →
  PrefixTuple f base extras domains₁ as → PrefixTuple f base extras domains₂ bs →
  apply q as = some r → apply r bs = some w →
  apply q (as.append bs) = some w ∨ Refines S (.marked f τ base extras) w

end LogicLineages.PersistentMarking.AuxiliaryTargets
