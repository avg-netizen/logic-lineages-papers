module

public import LogicLineages.NativeModule.PersistentMarking.DecisionObservationTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.DecisionOccurrenceProof
open Spine NameBridge DecisionObservations
mutual
 theorem sound (stack : List Ty) (t : Expr) (locals : List Ty) (q : Expr)
    (h : (locals,q) ∈ occurrences stack t) : Occurs stack t locals q := by
  cases t with
  | free σ x => simp only [occurrences,List.mem_singleton,Prod.mk.injEq] at h; obtain ⟨rfl,rfl⟩ := h; exact .root
  | bound σ i => simp only [occurrences,List.mem_singleton,Prod.mk.injEq] at h; obtain ⟨rfl,rfl⟩ := h; exact .root
  | lam σ t =>
    simp only [occurrences,List.mem_cons,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩|h
    · exact .root
    · exact .lam (sound (σ::stack) t locals q h)
  | head f bs =>
    simp only [occurrences,List.mem_cons,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩|h
    · exact .root
    · exact .head (soundArgs stack bs locals q h)
  | marked f τ bs es =>
    simp only [occurrences,List.mem_cons,Prod.mk.injEq,List.mem_append] at h
    rcases h with ⟨rfl,rfl⟩|(h|h)
    · exact .root
    · exact .markedBase (soundArgs stack bs locals q h)
    · exact .markedExtra (soundArgs stack es locals q h)
 termination_by sizeOf t
 theorem soundArgs (stack : List Ty) (ts : Args) (locals : List Ty) (q : Expr)
    (h : (locals,q) ∈ occurrencesArgs stack ts) : OccursArgs stack ts locals q := by
  cases ts with
  | nil => cases h
  | cons t ts =>
    rcases List.mem_append.mp h with h|h
    · exact .here (sound stack t locals q h)
    · exact .there (soundArgs stack ts locals q h)
 termination_by sizeOf ts
end

theorem complete (stack : List Ty) (t : Expr) (locals : List Ty) (q : Expr)
    (h : Occurs stack t locals q) : (locals,q) ∈ occurrences stack t := by
  induction h using Occurs.rec
    (motive_2 := fun stack ts locals q _ => (locals,q) ∈ occurrencesArgs stack ts) with
  | @root stack q => cases q <;> exact List.mem_cons_self
  | lam h ih => exact List.mem_cons_of_mem _ ih
  | head h ih => exact List.mem_cons_of_mem _ ih
  | markedBase h ih => exact List.mem_cons_of_mem _ (List.mem_append_left _ ih)
  | markedExtra h ih => exact List.mem_cons_of_mem _ (List.mem_append_right _ ih)
  | here h ih => exact List.mem_append_left _ ih
  | there h ih => exact List.mem_append_right _ ih

theorem enumeration (stack : List Ty) (t : Expr) (locals : List Ty) (q : Expr) :
    (locals,q) ∈ occurrences stack t ↔ Occurs stack t locals q := ⟨sound stack t locals q,complete stack t locals q⟩
end LogicLineages.PersistentMarking.DecisionOccurrenceProof
