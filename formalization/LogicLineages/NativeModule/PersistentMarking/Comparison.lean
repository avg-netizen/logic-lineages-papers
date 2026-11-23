module

public import LogicLineages.NativeModule.PersistentMarking.Signature
public import LogicLineages.NativeModule.PersistentMarking.Occurrences
public import LogicLineages.NativeModule.PersistentMarking.NameBridge
public import LogicLineages.NativeModule.PersistentMarking.SpineMarking

@[expose] public section

namespace LogicLineages.PersistentMarking.Spine
open NameBridge (openBody freeOccurs)

/- Finite least derivations. Endpoint premises impose the actual typed,
signature-valid auxiliary carrier; they assert no ordering closure property. -/
mutual
 inductive Weak (S : Signature) : Expr → Expr → Prop where
   | var : Weak S (.free σ x) (.free σ x)
   | abs : PaperTerm S (.lam σ s) (.arrow σ τ) →
       PaperTerm S (.lam σ t) (.arrow σ τ) →
       freeOccurs (σ,x) s = false → freeOccurs (σ,x) t = false →
       Weak S (openBody σ x s) (openBody σ x t) →
       Weak S (.lam σ s) (.lam σ t)
   | funHead : PaperTerm S (.head f ss) f.result →
       PaperTerm S (.head g ts) g.result → Equivalent S f g →
       f.result = g.result → Matching S ss ts → Weak S (.head f ss) (.head g ts)
   | put : PaperTerm S (.head f ss) f.result → PaperTerm S t f.result →
       Weak S (.marked f f.result ss .nil) t → Weak S (.head f ss) t
   | select : PaperTerm S (.marked f τ ss es) τ → PaperTerm S t τ →
       (At ss i q ∨ At es i q) → Typed EmptyContext q (ArrowPrefix domains τ) →
       apply q (ownerCopies f ss es domains) = some r → Weak S r t →
       Weak S (.marked f τ ss es) t
   | fabs : PaperTerm S (.marked f (.arrow σ τ) ss es) (.arrow σ τ) →
       PaperTerm S (.lam σ body) (.arrow σ τ) →
       freeOccurs (σ,x) (.marked f (.arrow σ τ) ss es) = false →
       freeOccurs (σ,x) body = false →
       Weak S (.marked f τ ss (es.append (.cons (.free σ x) .nil))) (openBody σ x body) →
       Weak S (.marked f (.arrow σ τ) ss es) (.lam σ body)
   | copy : PaperTerm S (.marked f g.result ss es) g.result →
       PaperTerm S (.head g ts) g.result → Precedes S f g →
       Whole S f ss es ts → Weak S (.marked f g.result ss es) (.head g ts)
   | stat : PaperTerm S (.marked f g.result ss es) g.result →
       PaperTerm S (.head g ts) g.result → Equivalent S f g →
       Multiset S ss ts → Whole S f ss es ts →
       Weak S (.marked f g.result ss es) (.head g ts)
 inductive Strict (S : Signature) : Expr → Expr → Prop where
   | intro : PaperTerm S q σ → PaperTerm S t σ →
       mark q = some r → Weak S r t → Strict S q t
 inductive Matching (S : Signature) : Args → Args → Prop where
   | nil : Matching S .nil .nil
   | cons : Remove targets y rest → Weak S x y → Matching S xs rest →
       Matching S (.cons x xs) targets
 inductive Multiset (S : Signature) : Args → Args → Prop where
   | replace : Split source kept removed → Split target matched added →
       Nonempty removed → Matching S kept matched → Coverage S removed added →
       Multiset S source target
 inductive Coverage (S : Signature) : Args → Args → Prop where
   | nil : Coverage S owners .nil
   | cons : At owners i q → Strict S q x → Coverage S owners xs →
       Coverage S owners (.cons x xs)
 inductive Whole (S : Signature) : Head → Args → Args → Args → Prop where
   | nil : Whole S f base extras .nil
   | cons : Weak S (.marked f q.type base extras) q → Whole S f base extras qs →
       Whole S f base extras (.cons q qs)
end
end LogicLineages.PersistentMarking.Spine
