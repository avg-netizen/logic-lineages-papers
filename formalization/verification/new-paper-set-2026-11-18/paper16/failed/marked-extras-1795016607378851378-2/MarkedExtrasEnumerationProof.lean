import LogicLineages.PersistentMarking.MarkedExtrasDownProof
namespace LogicLineages.PersistentMarking.MarkedExtrasEnumerationProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode MarkedExtras

theorem subsetsExact {α : Type} (us xs : List α) : xs ∈ subsets us ↔ xs.Sublist us := by
  induction us generalizing xs with
  | nil => simp [subsets]
  | cons a us ih =>
    simp only [subsets,List.mem_append,List.mem_map,ih,List.sublist_cons_iff]
    constructor
    · intro h
      rcases h with h|⟨ys,hy,he⟩
      · exact Or.inl h
      · exact Or.inr ⟨ys,he.symm,hy⟩
    · intro h
      rcases h with h|⟨ys,he,hy⟩
      · exact Or.inl h
      · exact Or.inr ⟨ys,hy,he.symm⟩

theorem sublistCanonical {α : Type} [DecidableEq α] {xs us : List α}
    (hs : xs.Sublist us) (hu : us.Pairwise (· ≠ ·)) : xs = us.filter (fun a => decide (a ∈ xs)) := by
  induction hs with
  | slnil => rfl
  | @cons xs us a hs ih =>
    obtain ⟨ha,ht⟩ := List.pairwise_cons.mp hu
    have hax : a ∉ xs := fun h => ha a (hs.subset h) rfl
    simpa only [List.filter_cons,show decide (a ∈ xs) = false by simp [hax],Bool.false_eq_true,if_false] using ih ht
  | @cons_cons xs us a hs ih =>
    obtain ⟨ha,ht⟩ := List.pairwise_cons.mp hu
    have he : us.filter (fun x => decide (x ∈ a::xs)) = us.filter (fun x => decide (x ∈ xs)) := by
      apply List.filter_congr
      intro x hx
      have hxa : x ≠ a := fun h => ha x hx h.symm
      simp only [List.mem_cons,hxa,false_or]
    simp only [List.filter_cons,List.mem_cons_self,decide_true,if_true,he]
    exact congrArg (a::·) (ih ht)

theorem closedExact (E : Environment) (Γ : Context) (xs : List Tagged) :
    closedBool E Γ xs = true ↔ DownClosed E Γ xs := by
  unfold closedBool DownClosed
  simp only [List.all_eq_true]
  constructor
  · intro h a ha b hb hle
    have h := h a ha b hb
    simpa only [hle,if_true,decide_eq_true_eq] using h
  · intro h a ha b hb
    by_cases hle : le E Γ b a = true
    · simpa only [hle,if_true,decide_eq_true_eq] using h a ha b hb hle
    · simp [hle]

theorem enumeration : MarkedExtrasTargets.Enumeration := by
  intro E Γ xs
  simp only [extras,List.mem_filter,subsetsExact,closedExact]
  constructor
  · rintro ⟨hs,hc⟩
    refine ⟨?_,hc⟩
    unfold Canonical
    exact sublistCanonical hs (MarkedExtrasFoundationProof.distinct E Γ)
  · rintro ⟨he,hc⟩
    refine ⟨?_,hc⟩
    rw [he]
    exact List.filter_sublist
end LogicLineages.PersistentMarking.MarkedExtrasEnumerationProof
