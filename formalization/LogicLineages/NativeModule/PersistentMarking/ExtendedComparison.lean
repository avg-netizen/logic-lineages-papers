module

public import LogicLineages.NativeModule.PersistentMarking.AuxiliaryWitnesses

@[expose] public section

namespace LogicLineages.PersistentMarking.Spine
open NameBridge (openBody freeOccurs)

/-- Disjoint judgment tags encode the same seven mutually recursive witness
sorts without generating seven copies of the large mutual recursor. -/
inductive ExtendedJudgment where
  | weak : Expr → Expr → ExtendedJudgment
  | strict : Expr → Expr → ExtendedJudgment
  | matching : Args → Args → ExtendedJudgment
  | multiset : Args → Args → ExtendedJudgment
  | coverage : Args → Args → ExtendedJudgment
  | whole : Head → Args → Args → Args → ExtendedJudgment
  | ordered : Args → Args → ExtendedJudgment

/- Explicit finite data trees, with every original premise retained. The tags
are disjoint; there is no cast between judgment sorts or embedding/cut oracle. -/
inductive ExtendedTree (S : Signature) : ExtendedJudgment → Type where
   | var : ExtendedTree S (.weak (.free σ x) (.free σ x))
   | abs : PaperTerm S (.lam σ s) (.arrow σ τ) →
       PaperTerm S (.lam σ t) (.arrow σ τ) →
       freeOccurs (σ,x) s = false → freeOccurs (σ,x) t = false →
       ExtendedTree S (.weak (openBody σ x s) (openBody σ x t)) →
       ExtendedTree S (.weak (.lam σ s) (.lam σ t))
   | funHead : PaperTerm S (.head f ss) f.result →
       PaperTerm S (.head g ts) g.result → Equivalent S f g →
       f.result = g.result → ExtendedTree S (.matching ss ts) → ExtendedTree S (.weak (.head f ss) (.head g ts))
   | put : PaperTerm S (.head f ss) f.result → PaperTerm S t f.result →
       ExtendedTree S (.weak (.marked f f.result ss .nil) t) → ExtendedTree S (.weak (.head f ss) t)
   | select : PaperTerm S (.marked f τ ss es) τ → PaperTerm S t τ →
       (At ss i q ∨ At es i q) → Typed EmptyContext q (ArrowPrefix domains τ) →
       apply q (ownerCopies f ss es domains) = some r → ExtendedTree S (.weak r t) →
       ExtendedTree S (.weak (.marked f τ ss es) t)
   | fabs : PaperTerm S (.marked f (.arrow σ τ) ss es) (.arrow σ τ) →
       PaperTerm S (.lam σ body) (.arrow σ τ) →
       freeOccurs (σ,x) (.marked f (.arrow σ τ) ss es) = false →
       freeOccurs (σ,x) body = false →
       ExtendedTree S (.weak (.marked f τ ss (es.append (.cons (.free σ x) .nil))) (openBody σ x body)) →
       ExtendedTree S (.weak (.marked f (.arrow σ τ) ss es) (.lam σ body))
   | copy : PaperTerm S (.marked f g.result ss es) g.result →
       PaperTerm S (.head g ts) g.result → Precedes S f g →
       ExtendedTree S (.whole f ss es ts) → ExtendedTree S (.weak (.marked f g.result ss es) (.head g ts))
   | stat : PaperTerm S (.marked f g.result ss es) g.result →
       PaperTerm S (.head g ts) g.result → Equivalent S f g →
       ExtendedTree S (.multiset ss ts) → ExtendedTree S (.whole f ss es ts) →
       ExtendedTree S (.weak (.marked f g.result ss es) (.head g ts))
   | inHead : PaperTerm S (.marked f τ ss es) τ → PaperTerm S (.marked g τ ts ds) τ →
       Equivalent S f g → ExtendedTree S (.matching ss ts) → ExtendedTree S (.ordered es ds) →
       ExtendedTree S (.weak (.marked f τ ss es) (.marked g τ ts ds))
   | marked1 : PaperTerm S (.marked f τ ss es) τ → PaperTerm S (.marked g τ ts ds) τ →
       Precedes S f g → ExtendedTree S (.whole f ss es ts) → ExtendedTree S (.whole f ss es ds) →
       ExtendedTree S (.weak (.marked f τ ss es) (.marked g τ ts ds))
   | marked2 : PaperTerm S (.marked f τ ss es) τ → PaperTerm S (.marked g τ ts ds) τ →
       Equivalent S f g → ExtendedTree S (.multiset ss ts) →
       ExtendedTree S (.whole f ss es ts) → ExtendedTree S (.whole f ss es ds) →
       ExtendedTree S (.weak (.marked f τ ss es) (.marked g τ ts ds))
   | drop : PaperTerm S (.marked f τ base (extras.append added)) τ → PaperTerm S t τ →
       ExtendedTree S (.weak (.marked f τ base extras) t) →
       ExtendedTree S (.weak (.marked f τ base (extras.append added)) t)
   | perm : PaperTerm S (.marked f τ base es) τ → PaperTerm S t τ →
       Permutation es ds → ExtendedTree S (.weak (.marked f τ base ds) t) →
       ExtendedTree S (.weak (.marked f τ base es) t)
   | copies : PaperTerm S (.marked f τ base extras) τ → PaperTerm S t τ →
       PrefixCopies f base extras ps → ExtendedTree S (.weak (.marked f τ base (extras.append ps)) t) →
       ExtendedTree S (.weak (.marked f τ base extras) t)
   | pselect : PaperTerm S (.marked f τ base extras) τ → PaperTerm S t τ →
       (At base i q ∨ At extras i q) → Typed EmptyContext q (ArrowPrefix domains τ) →
       PrefixTuple f base extras domains args → apply q args = some r → ExtendedTree S (.weak r t) →
       ExtendedTree S (.weak (.marked f τ base extras) t)
   | strictIntro : PaperTerm S q σ → PaperTerm S t σ →
       mark q = some r → ExtendedTree S (.weak r t) → ExtendedTree S (.strict q t)
   | matchingNil : ExtendedTree S (.matching .nil .nil)
   | matchingCons : Remove targets y rest → ExtendedTree S (.weak x y) → ExtendedTree S (.matching xs rest) →
       ExtendedTree S (.matching (.cons x xs) targets)
   | multisetReplace : Split source kept removed → Split target matched added →
       Nonempty removed → ExtendedTree S (.matching kept matched) → ExtendedTree S (.coverage removed added) →
       ExtendedTree S (.multiset source target)
   | coverageNil : ExtendedTree S (.coverage owners .nil)
   | coverageCons : At owners i q → ExtendedTree S (.strict q x) → ExtendedTree S (.coverage owners xs) →
       ExtendedTree S (.coverage owners (.cons x xs))
   | wholeNil : ExtendedTree S (.whole f base extras .nil)
   | wholeCons : ExtendedTree S (.weak (.marked f q.type base extras) q) → ExtendedTree S (.whole f base extras qs) →
       ExtendedTree S (.whole f base extras (.cons q qs))
   | orderedNil : ExtendedTree S (.ordered .nil .nil)
   | orderedCons : ExtendedTree S (.weak q t) → ExtendedTree S (.ordered qs ts) →
       ExtendedTree S (.ordered (.cons q qs) (.cons t ts))

abbrev ExtendedWeakTree (S : Signature) q t := ExtendedTree S (.weak q t)
abbrev ExtendedStrictTree (S : Signature) q t := ExtendedTree S (.strict q t)
abbrev ExtendedMatchingTree (S : Signature) xs ys := ExtendedTree S (.matching xs ys)
abbrev ExtendedMultisetTree (S : Signature) xs ys := ExtendedTree S (.multiset xs ys)
abbrev ExtendedCoverageTree (S : Signature) xs ys := ExtendedTree S (.coverage xs ys)
abbrev ExtendedWholeTree (S : Signature) f base extras qs := ExtendedTree S (.whole f base extras qs)
abbrev ExtendedOrderedTree (S : Signature) xs ys := ExtendedTree S (.ordered xs ys)

def ExtendedWeak (S : Signature) (q t : Expr) : Prop := _root_.Nonempty (ExtendedWeakTree S q t)
def ExtendedStrict (S : Signature) (q t : Expr) : Prop := _root_.Nonempty (ExtendedStrictTree S q t)
end LogicLineages.PersistentMarking.Spine
