module
public import LogicLineages.OrdinalComparison.SourceSpecialApplicationDefinitions
public import Mathlib.Data.List.Perm.Basic

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveComparison
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication

inductive HeadClass (Symbol : Type) where
  | application
  | native
  | ranked (s : Symbol)

def headClass {Symbol : Type} : Head Symbol → HeadClass Symbol
  | .application _ _ => .application
  | .ranked s => .ranked s
  | .zero | .succ | .cases _ | .recursor _ => .native

def headEquivalent {Symbol : Type} (f g : Head Symbol) : Prop := headClass f = headClass g

def headAbove {Symbol : Type} (rankedAbove : Symbol → Symbol → Prop) : Head Symbol → Head Symbol → Prop
  | .ranked f, .ranked g => rankedAbove f g
  | .ranked _, _ => True
  | .zero, .application _ _ | .succ, .application _ _ |
    .cases _, .application _ _ | .recursor _, .application _ _ => True
  | _, _ => False

abbrev Packed (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) := Σ τ, MarkedTerm Symbol arity Γ τ

def argumentList {Symbol : Type} {arity : Symbol → Nat} {Γ types : List Ty} :
    Arguments Symbol arity Γ types → List (Packed Symbol arity Γ)
  | .nil => []
  | .cons q rest => ⟨_,q⟩ :: argumentList rest

def strictMark {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty} :
    MarkedTerm Symbol arity Γ τ → Option (MarkedTerm Symbol arity Γ τ)
  | .var _ => none
  | .lam body => (strictMark body).map .lam
  | .ordinary f base => some (.marked f (headResult f) base [] .nil)
  | .marked _ _ _ _ _ => none

def selfArguments {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f))
    (extraTypes : List Ty) (extras : Arguments Symbol arity Γ extraTypes) :
    (types : List Ty) → Arguments Symbol arity Γ types
  | [] => .nil
  | τ::rest => .cons (.marked f τ base extraTypes extras) (selfArguments f base extraTypes extras rest)

def openMarked {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    (f : Head Symbol) (σ τ : Ty) (base : Arguments Symbol arity Γ (headArguments arity f))
    (extraTypes : List Ty) (extras : Arguments Symbol arity Γ extraTypes) : MarkedTerm Symbol arity (σ::Γ) τ :=
  .marked f τ (renameArguments base (Renaming.weaken Γ σ)) (extraTypes++[σ])
    (appendArguments (renameArguments extras (Renaming.weaken Γ σ)) (.cons (.var .here) .nil))

mutual
inductive Weak (Symbol : Type) (arity : Symbol → Nat) (rankedAbove : Symbol → Symbol → Prop) :
    (Γ : List Ty) → Packed Symbol arity Γ → Packed Symbol arity Γ → Prop where
  | var {Γ σ} (v : Variable Γ σ) : Weak Symbol arity rankedAbove Γ ⟨σ,.var v⟩ ⟨σ,.var v⟩
  | abs {Γ σ τ} (s t : MarkedTerm Symbol arity (σ::Γ) τ) :
      Weak Symbol arity rankedAbove (σ::Γ) ⟨τ,s⟩ ⟨τ,t⟩ →
      Weak Symbol arity rankedAbove Γ ⟨.arrow σ τ,.lam s⟩ ⟨.arrow σ τ,.lam t⟩
  | fun_ {Γ} (f g : Head Symbol) (ss : Arguments Symbol arity Γ (headArguments arity f))
      (ts : Arguments Symbol arity Γ (headArguments arity g)) (matched : List (Packed Symbol arity Γ)) :
      headEquivalent f g → headResult f=headResult g → (argumentList ts).Perm matched →
      WeakMatch Symbol arity rankedAbove Γ (argumentList ss) matched →
      Weak Symbol arity rankedAbove Γ ⟨_,.ordinary f ss⟩ ⟨_,.ordinary g ts⟩
  | put {Γ} (f : Head Symbol) (ss : Arguments Symbol arity Γ (headArguments arity f))
      (t : MarkedTerm Symbol arity Γ (headResult f)) :
      Weak Symbol arity rankedAbove Γ ⟨_,.marked f (headResult f) ss [] .nil⟩ ⟨_,t⟩ →
      Weak Symbol arity rankedAbove Γ ⟨_,.ordinary f ss⟩ ⟨_,t⟩
  | select {Γ σ τ} (f : Head Symbol) (ss : Arguments Symbol arity Γ (headArguments arity f))
      (extraTypes : List Ty) (extras : Arguments Symbol arity Γ extraTypes) (types : List Ty)
      (q : MarkedTerm Symbol arity Γ σ) (r t : MarkedTerm Symbol arity Γ τ) (suffix : σ=arrows types τ) :
      ⟨σ,q⟩ ∈ argumentList ss++argumentList extras →
      applyOriginalWith q (fun v => .var v) (selfArguments f ss extraTypes extras types) suffix=some r →
      Weak Symbol arity rankedAbove Γ ⟨τ,r⟩ ⟨τ,t⟩ →
      Weak Symbol arity rankedAbove Γ ⟨τ,.marked f τ ss extraTypes extras⟩ ⟨τ,t⟩
  | fAbs {Γ σ τ} (f : Head Symbol) (ss : Arguments Symbol arity Γ (headArguments arity f))
      (extraTypes : List Ty) (extras : Arguments Symbol arity Γ extraTypes)
      (t : MarkedTerm Symbol arity (σ::Γ) τ) :
      Weak Symbol arity rankedAbove (σ::Γ) ⟨τ,openMarked f σ τ ss extraTypes extras⟩ ⟨τ,t⟩ →
      Weak Symbol arity rankedAbove Γ ⟨.arrow σ τ,.marked f (.arrow σ τ) ss extraTypes extras⟩ ⟨.arrow σ τ,.lam t⟩
  | copy {Γ} (f g : Head Symbol) (ss : Arguments Symbol arity Γ (headArguments arity f))
      (extraTypes : List Ty) (extras : Arguments Symbol arity Γ extraTypes)
      (ts : Arguments Symbol arity Γ (headArguments arity g)) :
      headAbove rankedAbove f g →
      (∀ p ∈ argumentList ts, Weak Symbol arity rankedAbove Γ ⟨p.1,.marked f p.1 ss extraTypes extras⟩ p) →
      Weak Symbol arity rankedAbove Γ ⟨_,.marked f (headResult g) ss extraTypes extras⟩ ⟨_,.ordinary g ts⟩
  | stat {Γ} (f g : Head Symbol) (ss : Arguments Symbol arity Γ (headArguments arity f))
      (extraTypes : List Ty) (extras : Arguments Symbol arity Γ extraTypes)
      (ts : Arguments Symbol arity Γ (headArguments arity g)) :
      headEquivalent f g → StrictMultiset Symbol arity rankedAbove Γ (argumentList ss) (argumentList ts) →
      (∀ p ∈ argumentList ts, Weak Symbol arity rankedAbove Γ ⟨p.1,.marked f p.1 ss extraTypes extras⟩ p) →
      Weak Symbol arity rankedAbove Γ ⟨_,.marked f (headResult g) ss extraTypes extras⟩ ⟨_,.ordinary g ts⟩
inductive Strict (Symbol : Type) (arity : Symbol → Nat) (rankedAbove : Symbol → Symbol → Prop) :
    (Γ : List Ty) → Packed Symbol arity Γ → Packed Symbol arity Γ → Prop where
  | mark {Γ τ} (s r t : MarkedTerm Symbol arity Γ τ) : strictMark s=some r →
      Weak Symbol arity rankedAbove Γ ⟨τ,r⟩ ⟨τ,t⟩ → Strict Symbol arity rankedAbove Γ ⟨τ,s⟩ ⟨τ,t⟩
inductive WeakMatch (Symbol : Type) (arity : Symbol → Nat) (rankedAbove : Symbol → Symbol → Prop) :
    (Γ : List Ty) → List (Packed Symbol arity Γ) → List (Packed Symbol arity Γ) → Prop where
  | nil {Γ} : WeakMatch Symbol arity rankedAbove Γ [] []
  | cons {Γ} (s t : Packed Symbol arity Γ) (ss ts : List (Packed Symbol arity Γ)) :
      Weak Symbol arity rankedAbove Γ s t → WeakMatch Symbol arity rankedAbove Γ ss ts →
      WeakMatch Symbol arity rankedAbove Γ (s::ss) (t::ts)
inductive StrictMultiset (Symbol : Type) (arity : Symbol → Nat) (rankedAbove : Symbol → Symbol → Prop) :
    (Γ : List Ty) → List (Packed Symbol arity Γ) → List (Packed Symbol arity Γ) → Prop where
  | replace {Γ} (ss ts kept retained removed inserted : List (Packed Symbol arity Γ)) :
      ss.Perm (kept++removed) → ts.Perm (retained++inserted) → removed≠[] →
      WeakMatch Symbol arity rankedAbove Γ kept retained → ReplacementMatch Symbol arity rankedAbove Γ removed inserted →
      StrictMultiset Symbol arity rankedAbove Γ ss ts
inductive ReplacementMatch (Symbol : Type) (arity : Symbol → Nat) (rankedAbove : Symbol → Symbol → Prop) :
    (Γ : List Ty) → List (Packed Symbol arity Γ) → List (Packed Symbol arity Γ) → Prop where
  | nil {Γ} (removed : List (Packed Symbol arity Γ)) : ReplacementMatch Symbol arity rankedAbove Γ removed []
  | cons {Γ} (removed : List (Packed Symbol arity Γ)) (s t : Packed Symbol arity Γ) (rest : List (Packed Symbol arity Γ)) :
      s ∈ removed → Strict Symbol arity rankedAbove Γ s t → ReplacementMatch Symbol arity rankedAbove Γ removed rest →
      ReplacementMatch Symbol arity rankedAbove Γ removed (t::rest)
end

end LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveComparison
