module

public import LogicLineages.NativeModule.PersistentMarking.ObservationLambda

@[expose] public section

namespace LogicLineages.PersistentMarking.PortComparison
open Spine NameBridge DecisionPorts ObservationLambda
/- The literal six original judgments, indexed by actual used-port slots.
Only binder rules choose the first unused slot and consume it. -/
mutual
 inductive Weak (S : Signature) (K : List Ty) (V : List Name) : Context → Expr → Expr → Prop where
   | var : Weak S K V Γ (.free σ x) (.free σ x)
   | abs : PaperTerm S (.lam σ s) (.arrow σ τ) →
       PaperTerm S (.lam σ t) (.arrow σ τ) → σ ∈ K → firstUnused Γ = some i →
       freeOccurs (σ,portName V i) s = false → freeOccurs (σ,portName V i) t = false →
       Weak S K V (fillSlot Γ i σ) (openBody σ (portName V i) s) (openBody σ (portName V i) t) →
       Weak S K V Γ (.lam σ s) (.lam σ t)
   | funHead : PaperTerm S (.head f ss) f.result →
       PaperTerm S (.head g ts) g.result → Equivalent S f g →
       f.result = g.result → Matching S K V Γ ss ts → Weak S K V Γ (.head f ss) (.head g ts)
   | put : PaperTerm S (.head f ss) f.result → PaperTerm S t f.result →
       Weak S K V Γ (.marked f f.result ss .nil) t → Weak S K V Γ (.head f ss) t
   | select : PaperTerm S (.marked f τ ss es) τ → PaperTerm S t τ →
       (At ss i q ∨ At es i q) → Typed EmptyContext q (ArrowPrefix domains τ) →
       apply q (ownerCopies f ss es domains) = some r → Weak S K V Γ r t →
       Weak S K V Γ (.marked f τ ss es) t
   | fabs : PaperTerm S (.marked f (.arrow σ τ) ss es) (.arrow σ τ) →
       PaperTerm S (.lam σ body) (.arrow σ τ) → σ ∈ K → firstUnused Γ = some i →
       freeOccurs (σ,portName V i) (.marked f (.arrow σ τ) ss es) = false →
       freeOccurs (σ,portName V i) body = false →
       Weak S K V (fillSlot Γ i σ)
         (.marked f τ ss (es.append (.cons (.free σ (portName V i)) .nil)))
         (openBody σ (portName V i) body) →
       Weak S K V Γ (.marked f (.arrow σ τ) ss es) (.lam σ body)
   | copy : PaperTerm S (.marked f g.result ss es) g.result →
       PaperTerm S (.head g ts) g.result → Precedes S f g →
       Whole S K V Γ f ss es ts → Weak S K V Γ (.marked f g.result ss es) (.head g ts)
   | stat : PaperTerm S (.marked f g.result ss es) g.result →
       PaperTerm S (.head g ts) g.result → Equivalent S f g →
       Multiset S K V Γ ss ts → Whole S K V Γ f ss es ts →
       Weak S K V Γ (.marked f g.result ss es) (.head g ts)
 inductive Strict (S : Signature) (K : List Ty) (V : List Name) : Context → Expr → Expr → Prop where
   | intro : PaperTerm S q σ → PaperTerm S t σ →
       mark q = some r → Weak S K V Γ r t → Strict S K V Γ q t
 inductive Matching (S : Signature) (K : List Ty) (V : List Name) : Context → Args → Args → Prop where
   | nil : Matching S K V Γ .nil .nil
   | cons : Remove targets y rest → Weak S K V Γ x y → Matching S K V Γ xs rest →
       Matching S K V Γ (.cons x xs) targets
 inductive Multiset (S : Signature) (K : List Ty) (V : List Name) : Context → Args → Args → Prop where
   | replace : Split source kept removed → Split target matched added →
       Nonempty removed → Matching S K V Γ kept matched → Coverage S K V Γ removed added →
       Multiset S K V Γ source target
 inductive Coverage (S : Signature) (K : List Ty) (V : List Name) : Context → Args → Args → Prop where
   | nil : Coverage S K V Γ owners .nil
   | cons : At owners i q → Strict S K V Γ q x → Coverage S K V Γ owners xs →
       Coverage S K V Γ owners (.cons x xs)
 inductive Whole (S : Signature) (K : List Ty) (V : List Name) : Context → Head → Args → Args → Args → Prop where
   | nil : Whole S K V Γ f base extras .nil
   | cons : Weak S K V Γ (.marked f q.type base extras) q → Whole S K V Γ f base extras qs →
       Whole S K V Γ f base extras (.cons q qs)
end
end LogicLineages.PersistentMarking.PortComparison
