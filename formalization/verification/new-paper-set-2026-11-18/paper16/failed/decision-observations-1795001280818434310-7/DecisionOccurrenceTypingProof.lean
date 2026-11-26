import LogicLineages.PersistentMarking.DecisionObservationTargets
import LogicLineages.PersistentMarking.SpineShiftProof
namespace LogicLineages.PersistentMarking.DecisionOccurrenceProof
open Spine NameBridge DecisionObservations
mutual
 theorem typed (stack : List Ty) (t : Expr) (τ : Ty) (locals : List Ty) (q : Expr)
    (ht : Typed (BoundContext.prefix stack EmptyContext) t τ) (h : Occurs stack t locals q) :
    Typed (BoundContext.prefix locals EmptyContext) q q.type := by
  cases t with
  | free σ x => cases h; simpa only [Expr.type] using ht
  | bound σ i => cases h; simpa only [Expr.type] using ht
  | lam σ t =>
    cases h with
    | root => simpa only [SpineShiftProof.annotationExact _ _ _ ht] using ht
    | lam h => cases ht with | lam ht => exact typed (σ::stack) t _ locals q ht h
  | head f bs =>
    cases h with
    | root => simpa only [SpineShiftProof.annotationExact _ _ _ ht] using ht
    | head h => cases ht with | head ht => exact typedArgs stack bs _ locals q ht h
  | marked f τ bs es =>
    cases h with
    | root => simpa only [SpineShiftProof.annotationExact _ _ _ ht] using ht
    | markedBase h => cases ht with | marked hb he => exact typedArgs stack bs _ locals q hb h
    | markedExtra h => cases ht with | marked hb he => exact typedExtras stack es locals q he h
 termination_by sizeOf t
 theorem typedArgs (stack : List Ty) (ts : Args) (types : List Ty) (locals : List Ty) (q : Expr)
    (ht : BaseTyped (BoundContext.prefix stack EmptyContext) ts types) (h : OccursArgs stack ts locals q) :
    Typed (BoundContext.prefix locals EmptyContext) q q.type := by
  cases ts with
  | nil => cases h
  | cons t ts =>
    cases ht with
    | cons ht hts => cases h with
      | here h => exact typed stack t _ locals q ht h
      | there h => exact typedArgs stack ts _ locals q hts h
 termination_by sizeOf ts
 theorem typedExtras (stack : List Ty) (ts : Args) (locals : List Ty) (q : Expr)
    (ht : ExtrasTyped (BoundContext.prefix stack EmptyContext) ts) (h : OccursArgs stack ts locals q) :
    Typed (BoundContext.prefix locals EmptyContext) q q.type := by
  cases ts with
  | nil => cases h
  | cons t ts =>
    cases ht with
    | cons ht hts => cases h with
      | here h => exact typed stack t _ locals q ht h
      | there h => exact typedExtras stack ts locals q hts h
 termination_by sizeOf ts
end
end LogicLineages.PersistentMarking.DecisionOccurrenceProof
