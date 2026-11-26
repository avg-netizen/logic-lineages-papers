import LogicLineages.PersistentMarking.NumberedWindowSourceGuardTargets
import LogicLineages.PersistentMarking.NumberedWindowRealizationWindowProof

namespace LogicLineages.PersistentMarking.NumberedWindowSourceInventoryProof
open Spine NameBridge DecisionInventory DecisionPorts DecisionSourceUniverse NumberedWindowDomain

theorem supportArgs (K : List Ty) (V : List Name) (H : List Head) (Γ : Context) (xs : Spine.Args)
    (hSupport : SymbolicArgsAdmissible K xs)
    (hHeads : ∀ f, f ∈ headsArgs xs → f ∈ H)
    (hNames : ∀ n, n ∈ freeInventoryArgs xs → AllowedName V Γ n) :
    ArgsUniverse K V H Γ xs := by
  cases xs with
  | nil => trivial
  | cons a tail =>
    refine ⟨⟨?_,?_,?_⟩,supportArgs K V H Γ tail ?_ ?_ ?_⟩
    · intro τ h
      exact hSupport τ (List.mem_append_left _ h)
    · intro f h
      exact hHeads f (List.mem_append_left _ h)
    · intro n h
      exact hNames n (List.mem_append_left _ ((DecisionInventoryProof.freeExact a n).mpr h))
    · intro τ h
      exact hSupport τ (List.mem_append_right _ h)
    · intro f h
      exact hHeads f (List.mem_append_right _ h)
    · intro n h
      exact hNames n (List.mem_append_right _ h)
termination_by sizeOf xs

private def TermAdmitted (S : Signature) (q : Expr) : Prop :=
  (∀ f, f ∈ heads q → Admitted S f) → Valid S q

private def ArgsAdmitted (S : Signature) (xs : Spine.Args) : Prop :=
  (∀ f, f ∈ headsArgs xs → Admitted S f) → ValidArgs S xs

theorem validOfHeads (S : Signature) (q : Expr) : TermAdmitted S q := by
  apply @Expr.rec (TermAdmitted S) (ArgsAdmitted S)
  · intro σ x; exact fun _ => True.intro
  · intro σ i; exact fun _ => True.intro
  · intro σ q ih; exact ih
  · intro f bs ih h
    exact ⟨h f List.mem_cons_self,ih (fun g hg => h g (List.mem_cons_of_mem _ hg))⟩
  · intro f τ bs es ihb ihe h
    exact ⟨h f List.mem_cons_self,
      ihb (fun g hg => h g (List.mem_cons_of_mem _ (List.mem_append_left _ hg))),
      ihe (fun g hg => h g (List.mem_cons_of_mem _ (List.mem_append_right _ hg)))⟩
  · exact fun _ => True.intro
  · intro q qs ihq ihqs h
    exact ⟨ihq (fun g hg => h g (List.mem_append_left _ hg)),
      ihqs (fun g hg => h g (List.mem_append_right _ hg))⟩

theorem validArgsHeads (S : Signature) (xs : Spine.Args) (h : ValidArgs S xs) :
    ∀ f, f ∈ headsArgs xs → Admitted S f := by
  cases xs with
  | nil => intro f hf; cases hf
  | cons q tail =>
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact NumberedWindowRealizationWindowProof.admitted S q h.1 f hf
    · exact validArgsHeads S tail h.2 f hf
termination_by sizeOf xs

end LogicLineages.PersistentMarking.NumberedWindowSourceInventoryProof
