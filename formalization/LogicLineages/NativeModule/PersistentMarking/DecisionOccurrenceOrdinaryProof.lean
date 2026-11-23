module

public import LogicLineages.NativeModule.PersistentMarking.DecisionObservationTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.DecisionOccurrenceProof
open Spine NameBridge DecisionObservations
mutual
 theorem ordinary (stack : List Ty) (t : Expr) (locals : List Ty) (q : Expr)
    (ho : Ordinary t) (h : Occurs stack t locals q) : Ordinary q := by
  cases t with
  | free σ x => cases h; exact ho
  | bound σ i => cases h; exact ho
  | lam σ t => cases h with
    | root => exact ho
    | lam h => exact ordinary (σ::stack) t locals q ho h
  | head f bs => cases h with
    | root => exact ho
    | head h => exact ordinaryArgs stack bs locals q ho h
  | marked f τ bs es => exact False.elim ho
 termination_by sizeOf t
 theorem ordinaryArgs (stack : List Ty) (ts : Args) (locals : List Ty) (q : Expr)
    (ho : OrdinaryArgs ts) (h : OccursArgs stack ts locals q) : Ordinary q := by
  cases ts with
  | nil => cases h
  | cons t ts => cases h with
    | here h => exact ordinary stack t locals q ho.1 h
    | there h => exact ordinaryArgs stack ts locals q ho.2 h
 termination_by sizeOf ts
end
end LogicLineages.PersistentMarking.DecisionOccurrenceProof
