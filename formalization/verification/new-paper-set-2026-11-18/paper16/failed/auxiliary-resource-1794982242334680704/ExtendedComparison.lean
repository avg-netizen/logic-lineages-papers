import LogicLineages.PersistentMarking.AuxiliaryWitnesses
namespace LogicLineages.PersistentMarking.Spine
open NameBridge (openBody freeOccurs)

/- Actual finite auxiliary derivations. All recursive premises, including
Whole and ordered-extra matching, are data trees available to the cut measure.
No original-relation embedding or composition oracle is a constructor. -/
mutual
 inductive ExtendedWeakTree (S : Signature) : Expr → Expr → Type where
   | var : ExtendedWeakTree S (.free σ x) (.free σ x)
   | abs : PaperTerm S (.lam σ s) (.arrow σ τ) →
       PaperTerm S (.lam σ t) (.arrow σ τ) →
       freeOccurs (σ,x) s = false → freeOccurs (σ,x) t = false →
       ExtendedWeakTree S (openBody σ x s) (openBody σ x t) →
       ExtendedWeakTree S (.lam σ s) (.lam σ t)
   | funHead : PaperTerm S (.head f ss) f.result →
       PaperTerm S (.head g ts) g.result → Equivalent S f g →
       f.result = g.result → ExtendedMatchingTree S ss ts → ExtendedWeakTree S (.head f ss) (.head g ts)
   | put : PaperTerm S (.head f ss) f.result → PaperTerm S t f.result →
       ExtendedWeakTree S (.marked f f.result ss .nil) t → ExtendedWeakTree S (.head f ss) t
   | select : PaperTerm S (.marked f τ ss es) τ → PaperTerm S t τ →
       (At ss i q ∨ At es i q) → Typed EmptyContext q (ArrowPrefix domains τ) →
       apply q (ownerCopies f ss es domains) = some r → ExtendedWeakTree S r t →
       ExtendedWeakTree S (.marked f τ ss es) t
   | fabs : PaperTerm S (.marked f (.arrow σ τ) ss es) (.arrow σ τ) →
       PaperTerm S (.lam σ body) (.arrow σ τ) →
       freeOccurs (σ,x) (.marked f (.arrow σ τ) ss es) = false →
       freeOccurs (σ,x) body = false →
       ExtendedWeakTree S (.marked f τ ss (es.append (.cons (.free σ x) .nil))) (openBody σ x body) →
       ExtendedWeakTree S (.marked f (.arrow σ τ) ss es) (.lam σ body)
   | copy : PaperTerm S (.marked f g.result ss es) g.result →
       PaperTerm S (.head g ts) g.result → Precedes S f g →
       ExtendedWholeTree S f ss es ts → ExtendedWeakTree S (.marked f g.result ss es) (.head g ts)
   | stat : PaperTerm S (.marked f g.result ss es) g.result →
       PaperTerm S (.head g ts) g.result → Equivalent S f g →
       ExtendedMultisetTree S ss ts → ExtendedWholeTree S f ss es ts →
       ExtendedWeakTree S (.marked f g.result ss es) (.head g ts)
   | inHead : PaperTerm S (.marked f τ ss es) τ → PaperTerm S (.marked g τ ts ds) τ →
       Equivalent S f g → ExtendedMatchingTree S ss ts → ExtendedOrderedTree S es ds →
       ExtendedWeakTree S (.marked f τ ss es) (.marked g τ ts ds)
   | marked1 : PaperTerm S (.marked f τ ss es) τ → PaperTerm S (.marked g τ ts ds) τ →
       Precedes S f g → ExtendedWholeTree S f ss es ts → ExtendedWholeTree S f ss es ds →
       ExtendedWeakTree S (.marked f τ ss es) (.marked g τ ts ds)
   | marked2 : PaperTerm S (.marked f τ ss es) τ → PaperTerm S (.marked g τ ts ds) τ →
       Equivalent S f g → ExtendedMultisetTree S ss ts →
       ExtendedWholeTree S f ss es ts → ExtendedWholeTree S f ss es ds →
       ExtendedWeakTree S (.marked f τ ss es) (.marked g τ ts ds)
   | drop : PaperTerm S (.marked f τ base (extras.append added)) τ → PaperTerm S t τ →
       ExtendedWeakTree S (.marked f τ base extras) t →
       ExtendedWeakTree S (.marked f τ base (extras.append added)) t
   | perm : PaperTerm S (.marked f τ base es) τ → PaperTerm S t τ →
       Permutation es ds → ExtendedWeakTree S (.marked f τ base ds) t →
       ExtendedWeakTree S (.marked f τ base es) t
   | copies : PaperTerm S (.marked f τ base extras) τ → PaperTerm S t τ →
       PrefixCopies f base extras ps → ExtendedWeakTree S (.marked f τ base (extras.append ps)) t →
       ExtendedWeakTree S (.marked f τ base extras) t
   | pselect : PaperTerm S (.marked f τ base extras) τ → PaperTerm S t τ →
       (At base i q ∨ At extras i q) → Typed EmptyContext q (ArrowPrefix domains τ) →
       PrefixTuple f base extras domains args → apply q args = some r → ExtendedWeakTree S r t →
       ExtendedWeakTree S (.marked f τ base extras) t
 inductive ExtendedStrictTree (S : Signature) : Expr → Expr → Type where
   | intro : PaperTerm S q σ → PaperTerm S t σ →
       mark q = some r → ExtendedWeakTree S r t → ExtendedStrictTree S q t
 inductive ExtendedMatchingTree (S : Signature) : Args → Args → Type where
   | nil : ExtendedMatchingTree S .nil .nil
   | cons : Remove targets y rest → ExtendedWeakTree S x y → ExtendedMatchingTree S xs rest →
       ExtendedMatchingTree S (.cons x xs) targets
 inductive ExtendedMultisetTree (S : Signature) : Args → Args → Type where
   | replace : Split source kept removed → Split target matched added →
       Nonempty removed → ExtendedMatchingTree S kept matched → ExtendedCoverageTree S removed added →
       ExtendedMultisetTree S source target
 inductive ExtendedCoverageTree (S : Signature) : Args → Args → Type where
   | nil : ExtendedCoverageTree S owners .nil
   | cons : At owners i q → ExtendedStrictTree S q x → ExtendedCoverageTree S owners xs →
       ExtendedCoverageTree S owners (.cons x xs)
 inductive ExtendedWholeTree (S : Signature) : Head → Args → Args → Args → Type where
   | nil : ExtendedWholeTree S f base extras .nil
   | cons : ExtendedWeakTree S (.marked f q.type base extras) q → ExtendedWholeTree S f base extras qs →
       ExtendedWholeTree S f base extras (.cons q qs)
 inductive ExtendedOrderedTree (S : Signature) : Args → Args → Type where
   | nil : ExtendedOrderedTree S .nil .nil
   | cons : ExtendedWeakTree S q t → ExtendedOrderedTree S qs ts →
       ExtendedOrderedTree S (.cons q qs) (.cons t ts)
end

def ExtendedWeak (S : Signature) (q t : Expr) : Prop := _root_.Nonempty (ExtendedWeakTree S q t)
def ExtendedStrict (S : Signature) (q t : Expr) : Prop := _root_.Nonempty (ExtendedStrictTree S q t)
end LogicLineages.PersistentMarking.Spine
