import LogicLineages.PersistentMarking.DecisionObservationTargets
namespace LogicLineages.PersistentMarking.DecisionOccurrenceProof
open Spine NameBridge DecisionObservations
mutual
 theorem valid (S : Signature) (stack : List Ty) (t : Expr) (locals : List Ty) (q : Expr)
    (hv : Valid S t) (h : Occurs stack t locals q) : Valid S q := by
  cases t with
  | free σ x => cases h; exact hv
  | bound σ i => cases h; exact hv
  | lam σ t => cases h with
    | root => exact hv
    | lam h => exact valid S (σ::stack) t locals q hv h
  | head f bs => cases h with
    | root => exact hv
    | head h => exact validArgs S stack bs locals q hv.2 h
  | marked f τ bs es => cases h with
    | root => exact hv
    | markedBase h => exact validArgs S stack bs locals q hv.2.1 h
    | markedExtra h => exact validArgs S stack es locals q hv.2.2 h
 termination_by sizeOf t
 theorem validArgs (S : Signature) (stack : List Ty) (ts : Args) (locals : List Ty) (q : Expr)
    (hv : ValidArgs S ts) (h : OccursArgs stack ts locals q) : Valid S q := by
  cases ts with
  | nil => cases h
  | cons t ts => cases h with
    | here h => exact valid S stack t locals q hv.1 h
    | there h => exact validArgs S stack ts locals q hv.2 h
 termination_by sizeOf ts
end
end LogicLineages.PersistentMarking.DecisionOccurrenceProof
