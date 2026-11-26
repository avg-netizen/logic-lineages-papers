import LogicLineages.PersistentMarking.DecisionObservationTargets
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
end LogicLineages.PersistentMarking.DecisionOccurrenceProof
