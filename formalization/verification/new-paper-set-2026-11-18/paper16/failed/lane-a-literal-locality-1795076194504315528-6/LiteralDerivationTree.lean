import LogicLineages.PersistentMarking.Comparison

namespace LogicLineages.PersistentMarking.LiteralDerivationTree
open Spine NameBridge

/-- Exactly the six original judgment sorts, without the auxiliary
marked-target relation's additional clauses or ordered-list sort. -/
inductive Judgment where
  | weak : Expr → Expr → Judgment
  | strict : Expr → Expr → Judgment
  | matching : Args → Args → Judgment
  | multiset : Args → Args → Judgment
  | coverage : Args → Args → Judgment
  | whole : Head → Args → Args → Args → Judgment

def Holds (S : Signature) : Judgment → Prop
  | .weak q t => Weak S q t
  | .strict q t => Strict S q t
  | .matching qs ts => Matching S qs ts
  | .multiset qs ts => Multiset S qs ts
  | .coverage qs ts => Coverage S qs ts
  | .whole f bs es ts => Whole S f bs es ts

/-- Literal finite data certificates. Only the proof-sort recursive
premises are changed from Prop to data; types, positions, head guards,
literal calls, and all syntax indices are the original premises. -/
inductive Tree (S : Signature) : Judgment → Type where
  | var (σ : Ty) (x : Nat) : Tree S (.weak (.free σ x) (.free σ x))
  | abs (σ τ : Ty) (s t : Expr) (x : Nat) :
      PaperTerm S (.lam σ s) (.arrow σ τ) →
      PaperTerm S (.lam σ t) (.arrow σ τ) →
      freeOccurs (σ,x) s = false → freeOccurs (σ,x) t = false →
      Tree S (.weak (openBody σ x s) (openBody σ x t)) →
      Tree S (.weak (.lam σ s) (.lam σ t))
  | funHead (f g : Head) (ss ts : Args) :
      PaperTerm S (.head f ss) f.result →
      PaperTerm S (.head g ts) g.result → Equivalent S f g →
      f.result = g.result → Tree S (.matching ss ts) →
      Tree S (.weak (.head f ss) (.head g ts))
  | put (f : Head) (ss : Args) (t : Expr) :
      PaperTerm S (.head f ss) f.result → PaperTerm S t f.result →
      Tree S (.weak (.marked f f.result ss .nil) t) →
      Tree S (.weak (.head f ss) t)
  | select (f : Head) (τ : Ty) (ss es : Args) (t : Expr) (i : Nat)
      (q : Expr) (domains : List Ty) (r : Expr) :
      PaperTerm S (.marked f τ ss es) τ → PaperTerm S t τ →
      (At ss i q ∨ At es i q) → Typed EmptyContext q (ArrowPrefix domains τ) →
      apply q (ownerCopies f ss es domains) = some r → Tree S (.weak r t) →
      Tree S (.weak (.marked f τ ss es) t)
  | fabs (f : Head) (σ τ : Ty) (ss es : Args) (body : Expr) (x : Nat) :
      PaperTerm S (.marked f (.arrow σ τ) ss es) (.arrow σ τ) →
      PaperTerm S (.lam σ body) (.arrow σ τ) →
      freeOccurs (σ,x) (.marked f (.arrow σ τ) ss es) = false →
      freeOccurs (σ,x) body = false →
      Tree S (.weak (.marked f τ ss (es.append (.cons (.free σ x) .nil))) (openBody σ x body)) →
      Tree S (.weak (.marked f (.arrow σ τ) ss es) (.lam σ body))
  | copy (f g : Head) (ss es ts : Args) :
      PaperTerm S (.marked f g.result ss es) g.result →
      PaperTerm S (.head g ts) g.result → Precedes S f g →
      Tree S (.whole f ss es ts) →
      Tree S (.weak (.marked f g.result ss es) (.head g ts))
  | stat (f g : Head) (ss es ts : Args) :
      PaperTerm S (.marked f g.result ss es) g.result →
      PaperTerm S (.head g ts) g.result → Equivalent S f g →
      Tree S (.multiset ss ts) → Tree S (.whole f ss es ts) →
      Tree S (.weak (.marked f g.result ss es) (.head g ts))
  | strictIntro (q t r : Expr) (σ : Ty) :
      PaperTerm S q σ → PaperTerm S t σ → mark q = some r →
      Tree S (.weak r t) → Tree S (.strict q t)
  | matchingNil : Tree S (.matching .nil .nil)
  | matchingCons (x y : Expr) (xs targets rest : Args) :
      Remove targets y rest → Tree S (.weak x y) → Tree S (.matching xs rest) →
      Tree S (.matching (.cons x xs) targets)
  | multisetReplace (source kept removed target matched added : Args) :
      Split source kept removed → Split target matched added →
      Nonempty removed → Tree S (.matching kept matched) →
      Tree S (.coverage removed added) → Tree S (.multiset source target)
  | coverageNil (owners : Args) : Tree S (.coverage owners .nil)
  | coverageCons (owners : Args) (i : Nat) (q x : Expr) (xs : Args) :
      At owners i q → Tree S (.strict q x) → Tree S (.coverage owners xs) →
      Tree S (.coverage owners (.cons x xs))
  | wholeNil (f : Head) (base extras : Args) :
      Tree S (.whole f base extras .nil)
  | wholeCons (f : Head) (q : Expr) (base extras qs : Args) :
      Tree S (.weak (.marked f q.type base extras) q) →
      Tree S (.whole f base extras qs) → Tree S (.whole f base extras (.cons q qs))

end LogicLineages.PersistentMarking.LiteralDerivationTree
