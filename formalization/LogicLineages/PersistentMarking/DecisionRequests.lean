import LogicLineages.PersistentMarking.PortNormalization
namespace LogicLineages.PersistentMarking.DecisionRequests
open Spine NameBridge DecisionPorts ObservationLambda PortNormalization

/- Six comparison sorts and the actual full-tuple operation that Select
attempts before it has any comparison result. No proof success is stored. -/
inductive Request where
  | weak : Context → Expr → Expr → Request
  | strict : Context → Expr → Expr → Request
  | matching : Context → Args → Args → Request
  | multiset : Context → Args → Args → Request
  | coverage : Context → Args → Args → Request
  | whole : Context → Head → Args → Args → Args → Request
  | fullCall : Context → Expr → Ty → Args → Ty → Expr → Request

def blank (B : Nat) : Context := List.replicate B none

def Invariant (F : Inputs S) : Request → Prop
  | .weak Γ q t | .strict Γ q t =>
      WellFormed F.data.types F.data.ports Γ ∧ Source F Γ q ∧ Observed F Γ t
  | .matching Γ qs ts | .multiset Γ qs ts | .coverage Γ qs ts =>
      WellFormed F.data.types F.data.ports Γ ∧ Sources F Γ qs ∧ ObservedArgs F Γ ts
  | .whole Γ f bs es ts =>
      WellFormed F.data.types F.data.ports Γ ∧ OwnerSource F Γ f bs es ∧ ObservedArgs F Γ ts
  | .fullCall Γ q σ args τ t =>
      WellFormed F.data.types F.data.ports Γ ∧ Source F Γ q ∧ Sources F Γ args ∧
      Observed F Γ t ∧ σ ∈ F.data.types ∧ τ ∈ F.data.types ∧
      Typed EmptyContext q σ ∧ CallTyped EmptyContext σ args τ

/- Local requests are independent of success of every child and sibling
comparison. Only guards that enable that recursive request are retained. -/
inductive Child (S : Signature) (K : List Ty) (V : List Name) : Request → Request → Prop where
  | abs : PaperTerm S (.lam σ s) (.arrow σ τ) →
      PaperTerm S (.lam σ t) (.arrow σ τ) → firstUnused Γ = some i →
      Child S K V (.weak Γ (.lam σ s) (.lam σ t))
        (.weak (fillSlot Γ i σ) (openBody σ (portName V i) s) (openBody σ (portName V i) t))
  | funHead : PaperTerm S (.head f ss) f.result → PaperTerm S (.head g ts) g.result →
      Equivalent S f g → f.result = g.result →
      Child S K V (.weak Γ (.head f ss) (.head g ts)) (.matching Γ ss ts)
  | put : PaperTerm S (.head f ss) f.result → PaperTerm S t f.result →
      Child S K V (.weak Γ (.head f ss) t) (.weak Γ (.marked f f.result ss .nil) t)
  | select : PaperTerm S (.marked f τ ss es) τ → PaperTerm S t τ →
      (At ss i q ∨ At es i q) → Typed EmptyContext q (ArrowPrefix domains τ) →
      Child S K V (.weak Γ (.marked f τ ss es) t)
        (.fullCall Γ q (ArrowPrefix domains τ) (ownerCopies f ss es domains) τ t)
  | callResult : apply q args = some r →
      Child S K V (.fullCall Γ q σ args τ t) (.weak Γ r t)
  | fabs : PaperTerm S (.marked f (.arrow σ τ) ss es) (.arrow σ τ) →
      PaperTerm S (.lam σ body) (.arrow σ τ) → firstUnused Γ = some i →
      Child S K V (.weak Γ (.marked f (.arrow σ τ) ss es) (.lam σ body))
        (.weak (fillSlot Γ i σ) (.marked f τ ss (es.append (.cons (.free σ (portName V i)) .nil)))
          (openBody σ (portName V i) body))
  | copy : PaperTerm S (.marked f g.result ss es) g.result → PaperTerm S (.head g ts) g.result →
      Precedes S f g → Child S K V (.weak Γ (.marked f g.result ss es) (.head g ts))
        (.whole Γ f ss es ts)
  | statBase : PaperTerm S (.marked f g.result ss es) g.result → PaperTerm S (.head g ts) g.result →
      Equivalent S f g → Child S K V (.weak Γ (.marked f g.result ss es) (.head g ts))
        (.multiset Γ ss ts)
  | statWhole : PaperTerm S (.marked f g.result ss es) g.result → PaperTerm S (.head g ts) g.result →
      Equivalent S f g → Child S K V (.weak Γ (.marked f g.result ss es) (.head g ts))
        (.whole Γ f ss es ts)
  | strict : PaperTerm S q σ → PaperTerm S t σ → mark q = some r →
      Child S K V (.strict Γ q t) (.weak Γ r t)
  | matchingHead : Remove targets y rest →
      Child S K V (.matching Γ (.cons x xs) targets) (.weak Γ x y)
  | matchingTail : Remove targets y rest →
      Child S K V (.matching Γ (.cons x xs) targets) (.matching Γ xs rest)
  | multisetMatch : Split source kept removed → Split target matched added → Nonempty removed →
      Child S K V (.multiset Γ source target) (.matching Γ kept matched)
  | multisetCover : Split source kept removed → Split target matched added → Nonempty removed →
      Child S K V (.multiset Γ source target) (.coverage Γ removed added)
  | coverageHead : At owners i q →
      Child S K V (.coverage Γ owners (.cons x xs)) (.strict Γ q x)
  | coverageTail : At owners i q →
      Child S K V (.coverage Γ owners (.cons x xs)) (.coverage Γ owners xs)
  | wholeHead : Child S K V (.whole Γ f bs es (.cons q qs)) (.weak Γ (.marked f q.type bs es) q)
  | wholeTail : Child S K V (.whole Γ f bs es (.cons q qs)) (.whole Γ f bs es qs)

inductive Reach (S : Signature) (K : List Ty) (V : List Name) (root : Request) : Request → Prop where
  | root : Reach S K V root root
  | step : Reach S K V root parent → Child S K V parent child → Reach S K V root child

end LogicLineages.PersistentMarking.DecisionRequests
