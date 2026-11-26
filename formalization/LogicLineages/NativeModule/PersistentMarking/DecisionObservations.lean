module

public import LogicLineages.NativeModule.PersistentMarking.DecisionPorts

@[expose] public section

namespace LogicLineages.PersistentMarking.DecisionObservations
open Spine NameBridge DecisionInventory DecisionPorts

/- Nearest enclosing binder first. At the root the ambient bound context is
EmptyContext. Repeated subterms remain repeated list entries. -/
mutual
 def occurrences (stack : List Ty) : Expr → List (List Ty × Expr)
   | .free σ x => [(stack,.free σ x)]
   | .bound σ i => [(stack,.bound σ i)]
   | .lam σ q => (stack,.lam σ q) :: occurrences (σ::stack) q
   | .head f bs => (stack,.head f bs) :: occurrencesArgs stack bs
   | .marked f τ bs es => (stack,.marked f τ bs es) :: (occurrencesArgs stack bs ++ occurrencesArgs stack es)
 def occurrencesArgs (stack : List Ty) : Args → List (List Ty × Expr)
   | .nil => []
   | .cons q qs => occurrences stack q ++ occurrencesArgs stack qs
end

mutual
 inductive Occurs : List Ty → Expr → List Ty → Expr → Prop where
   | root : Occurs stack q stack q
   | lam : Occurs (σ::stack) body locals q → Occurs stack (.lam σ body) locals q
   | head : OccursArgs stack bs locals q → Occurs stack (.head f bs) locals q
   | markedBase : OccursArgs stack bs locals q → Occurs stack (.marked f τ bs es) locals q
   | markedExtra : OccursArgs stack es locals q → Occurs stack (.marked f τ bs es) locals q
 inductive OccursArgs : List Ty → Args → List Ty → Expr → Prop where
   | here : Occurs stack q locals r → OccursArgs stack (.cons q qs) locals r
   | there : OccursArgs stack qs locals r → OccursArgs stack (.cons q qs) locals r
end

def assignments (V : List Name) (Γ : Context) : List Ty → List Args
  | [] => [.nil]
  | σ::stack => (values V Γ σ).flatMap fun q => (assignments V Γ stack).map (.cons q)
inductive Assignment (V : List Name) (Γ : Context) : List Ty → Args → Prop where
  | nil : Assignment V Γ [] .nil
  | cons : AtPort V Γ σ q → Assignment V Γ stack qs → Assignment V Γ (σ::stack) (.cons q qs)

def openOccurrence (vs : Args) (q : Expr) : Expr := substitute vs 0 q

def observations (V : List Name) (B : Nat) (Γ : Context) (t : Expr) (σ : Ty) : List Expr :=
  (occurrences [] t).flatMap fun entry =>
    if entry.2.type = σ ∧ lambdaDepth entry.2 + used Γ ≤ B then
      (assignments V Γ entry.1).map (fun vs => openOccurrence vs entry.2)
    else []

/- This literal specification admits every compatible port assignment, with
reuse and extra occupied slots. It is not restricted to canonical openings. -/
def Observation (V : List Name) (B : Nat) (Γ : Context) (t : Expr) (σ : Ty) (r : Expr) : Prop :=
  ∃ stack q vs, Occurs [] t stack q ∧ Assignment V Γ stack vs ∧
    q.type = σ ∧ lambdaDepth q + used Γ ≤ B ∧ r = openOccurrence vs q
end LogicLineages.PersistentMarking.DecisionObservations
