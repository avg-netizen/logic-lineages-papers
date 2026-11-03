module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveComparisonDefinitions

@[expose] public section
/-! Typed bottom-free/no-meta auxiliary extension following Kop2012§5.4.1.
The ORIGINAL recursive comparison is imported unchanged. DropMore/Reorder are
explicit finite macros of the published extra rules; prefix copy witnesses
are literal typed source prefixes. No source equivalence, transitivity,
strong pair or normalization law is assumed by these definitions. -/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedComparison
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison

inductive Prefix {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} :
    {xs ys : List Ty} → Arguments Symbol arity Gamma xs → Arguments Symbol arity Gamma ys → Prop where
  | nil {ys : List Ty} (whole : Arguments Symbol arity Gamma ys) : Prefix .nil whole
  | cons {tau : Ty} {xs ys : List Ty} (q : MarkedTerm Symbol arity Gamma tau)
      (a : Arguments Symbol arity Gamma xs) (b : Arguments Symbol arity Gamma ys) :
      Prefix a b → Prefix (.cons q a) (.cons q b)

inductive PrefixCopies {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    {sourceTypes : List Ty} (sourceExtras : Arguments Symbol arity Gamma sourceTypes) :
    {types : List Ty} → Arguments Symbol arity Gamma types → Prop where
  | nil : PrefixCopies f base sourceExtras .nil
  | cons (tau : Ty) (preTypes restTypes : List Ty)
      (pre : Arguments Symbol arity Gamma preTypes) (rest : Arguments Symbol arity Gamma restTypes) :
      Prefix pre sourceExtras → PrefixCopies f base sourceExtras rest →
      PrefixCopies f base sourceExtras (.cons (.marked f tau base preTypes pre) rest)

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
  /-- A finite typed auxiliary presentation of Kop's extended In clause. -/
  | in_ {Γ τ} (f g : Head Symbol)
      (ss : Arguments Symbol arity Γ (headArguments arity f))
      (ts : Arguments Symbol arity Γ (headArguments arity g))
      (typesS : List Ty) (extrasS : Arguments Symbol arity Γ typesS)
      (typesT : List Ty) (extrasT : Arguments Symbol arity Γ typesT)
      (matched : List (Packed Symbol arity Γ)) :
      headEquivalent f g → (argumentList ts).Perm matched →
      WeakMatch Symbol arity rankedAbove Γ (argumentList ss) matched →
      WeakMatch Symbol arity rankedAbove Γ (argumentList extrasS) (argumentList extrasT) →
      Weak Symbol arity rankedAbove Γ ⟨τ,.marked f τ ss typesS extrasS⟩ ⟨τ,.marked g τ ts typesT extrasT⟩
  | marked1 {Γ τ} (f g : Head Symbol)
      (ss : Arguments Symbol arity Γ (headArguments arity f))
      (typesS : List Ty) (extrasS : Arguments Symbol arity Γ typesS)
      (ts : Arguments Symbol arity Γ (headArguments arity g))
      (typesT : List Ty) (extrasT : Arguments Symbol arity Γ typesT) :
      headAbove rankedAbove f g →
      (∀ p∈argumentList ts++argumentList extrasT,
        Weak Symbol arity rankedAbove Γ ⟨p.1,.marked f p.1 ss typesS extrasS⟩ p) →
      Weak Symbol arity rankedAbove Γ ⟨τ,.marked f τ ss typesS extrasS⟩ ⟨τ,.marked g τ ts typesT extrasT⟩
  | marked2 {Γ τ} (f g : Head Symbol)
      (ss : Arguments Symbol arity Γ (headArguments arity f))
      (typesS : List Ty) (extrasS : Arguments Symbol arity Γ typesS)
      (ts : Arguments Symbol arity Γ (headArguments arity g))
      (typesT : List Ty) (extrasT : Arguments Symbol arity Γ typesT) :
      headEquivalent f g → StrictMultiset Symbol arity rankedAbove Γ (argumentList ss) (argumentList ts) →
      (∀ p∈argumentList ts++argumentList extrasT,
        Weak Symbol arity rankedAbove Γ ⟨p.1,.marked f p.1 ss typesS extrasS⟩ p) →
      Weak Symbol arity rankedAbove Γ ⟨τ,.marked f τ ss typesS extrasS⟩ ⟨τ,.marked g τ ts typesT extrasT⟩
  /-- Macro for finitely many final-extra Drop clauses, not a new original rule. -/
  | dropMore {Γ τ} (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f))
      (types moreTypes : List Ty) (extras : Arguments Symbol arity Γ types)
      (more : Arguments Symbol arity Γ moreTypes) (t : MarkedTerm Symbol arity Γ τ) :
      Weak Symbol arity rankedAbove Γ ⟨τ,.marked f τ base types extras⟩ ⟨τ,t⟩ →
      Weak Symbol arity rankedAbove Γ
        ⟨τ,.marked f τ base (types++moreTypes) (appendArguments extras more)⟩ ⟨τ,t⟩
  /-- General finite-permutation presentation of the extra-only Swap macro.
  Its conservativity is an obligation; no claim of byte-identical source syntax. -/
  | reorder {Γ τ} (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f))
      (typesS typesT : List Ty) (extrasS : Arguments Symbol arity Γ typesS)
      (extrasT : Arguments Symbol arity Γ typesT) (t : MarkedTerm Symbol arity Γ τ) :
      (argumentList extrasS).Perm (argumentList extrasT) →
      Weak Symbol arity rankedAbove Γ ⟨τ,.marked f τ base typesT extrasT⟩ ⟨τ,t⟩ →
      Weak Symbol arity rankedAbove Γ ⟨τ,.marked f τ base typesS extrasS⟩ ⟨τ,t⟩
  | addPrefixCopies {Γ τ} (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f))
      (types copyTypes : List Ty) (extras : Arguments Symbol arity Γ types)
      (copies : Arguments Symbol arity Γ copyTypes) (t : MarkedTerm Symbol arity Γ τ) :
      PrefixCopies f base extras copies →
      Weak Symbol arity rankedAbove Γ
        ⟨τ,.marked f τ base (types++copyTypes) (appendArguments extras copies)⟩ ⟨τ,t⟩ →
      Weak Symbol arity rankedAbove Γ ⟨τ,.marked f τ base types extras⟩ ⟨τ,t⟩
  | prefixSelect {Γ σ τ} (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f))
      (extraTypes types : List Ty) (extras : Arguments Symbol arity Γ extraTypes)
      (copies : Arguments Symbol arity Γ types)
      (q : MarkedTerm Symbol arity Γ σ) (r t : MarkedTerm Symbol arity Γ τ)
      (suffix : σ=arrows types τ) :
      (⟨σ,q⟩ : Packed Symbol arity Γ)∈argumentList base++argumentList extras →
      PrefixCopies f base extras copies → applyOriginalWith q (fun v => .var v) copies suffix=some r →
      Weak Symbol arity rankedAbove Γ ⟨τ,r⟩ ⟨τ,t⟩ →
      Weak Symbol arity rankedAbove Γ ⟨τ,.marked f τ base extraTypes extras⟩ ⟨τ,t⟩
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

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedComparison
