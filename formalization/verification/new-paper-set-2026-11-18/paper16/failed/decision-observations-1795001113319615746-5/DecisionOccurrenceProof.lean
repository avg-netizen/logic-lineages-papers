import LogicLineages.PersistentMarking.DecisionObservationTargets
import LogicLineages.PersistentMarking.SpineShiftProof
namespace LogicLineages.PersistentMarking.DecisionOccurrenceProof
open Spine NameBridge DecisionObservations
mutual
 theorem enumeration (stack : List Ty) (t : Expr) (locals : List Ty) (q : Expr) :
    (locals,q) ∈ occurrences stack t ↔ Occurs stack t locals q := by
  cases t with
  | free σ x =>
    constructor
    · intro h; simp only [occurrences,List.mem_singleton,Prod.mk.injEq] at h; obtain ⟨rfl,rfl⟩ := h; exact .root
    · intro h; cases h; simp [occurrences]
  | bound σ i =>
    constructor
    · intro h; simp only [occurrences,List.mem_singleton,Prod.mk.injEq] at h; obtain ⟨rfl,rfl⟩ := h; exact .root
    · intro h; cases h; simp [occurrences]
  | lam σ t =>
    constructor
    · intro h; simp only [occurrences,List.mem_cons,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩|h
      · exact .root
      · exact .lam ((enumeration (σ::stack) t locals q).mp h)
    · intro h; cases h with
      | root => exact List.mem_cons_self
      | lam h => exact List.mem_cons_of_mem _ ((enumeration (σ::stack) t locals q).mpr h)
  | head f bs =>
    constructor
    · intro h; simp only [occurrences,List.mem_cons,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩|h
      · exact .root
      · exact .head ((enumerationArgs stack bs locals q).mp h)
    · intro h; cases h with
      | root => exact List.mem_cons_self
      | head h => exact List.mem_cons_of_mem _ ((enumerationArgs stack bs locals q).mpr h)
  | marked f τ bs es =>
    constructor
    · intro h; simp only [occurrences,List.mem_cons,Prod.mk.injEq,List.mem_append] at h
      rcases h with ⟨rfl,rfl⟩|(h|h)
      · exact .root
      · exact .markedBase ((enumerationArgs stack bs locals q).mp h)
      · exact .markedExtra ((enumerationArgs stack es locals q).mp h)
    · intro h; cases h with
      | root => exact List.mem_cons_self
      | markedBase h => exact List.mem_cons_of_mem _ (List.mem_append_left _ ((enumerationArgs stack bs locals q).mpr h))
      | markedExtra h => exact List.mem_cons_of_mem _ (List.mem_append_right _ ((enumerationArgs stack es locals q).mpr h))
 termination_by sizeOf t
 theorem enumerationArgs (stack : List Ty) (ts : Args) (locals : List Ty) (q : Expr) :
    (locals,q) ∈ occurrencesArgs stack ts ↔ OccursArgs stack ts locals q := by
  cases ts with
  | nil => constructor <;> intro h <;> cases h
  | cons t ts =>
    constructor
    · intro h; rcases List.mem_append.mp h with h|h
      · exact .here ((enumeration stack t locals q).mp h)
      · exact .there ((enumerationArgs stack ts locals q).mp h)
    · intro h; cases h with
      | here h => exact List.mem_append_left _ ((enumeration stack t locals q).mpr h)
      | there h => exact List.mem_append_right _ ((enumerationArgs stack ts locals q).mpr h)
 termination_by sizeOf ts
end
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
