import LogicLineages.PersistentMarking.FiniteDomainFoundationTargets
namespace LogicLineages.PersistentMarking.FinitePrefixProof
open Spine NameBridge FiniteDomainFoundation

theorem forward (σ : Ty) (domains : List Ty) (τ : Ty)
    (h : (domains,τ) ∈ fullPrefixes σ) : domains ≠ [] ∧ ArrowPrefix domains τ = σ := by
  induction σ generalizing domains τ with
  | ground => cases h
  | arrow α β iha ihb =>
    rcases List.mem_cons.mp h with h|h
    · cases h; exact ⟨by simp,rfl⟩
    · obtain ⟨⟨ds,υ⟩,hd,he⟩ := List.mem_map.mp h
      cases he
      exact ⟨by simp,congrArg (Ty.arrow α) (ihb _ _ hd).2⟩

theorem backward (domains : List Ty) (τ : Ty) (hn : domains ≠ []) :
    (domains,τ) ∈ fullPrefixes (ArrowPrefix domains τ) := by
  induction domains with
  | nil => exact False.elim (hn rfl)
  | cons α ds ih =>
    cases ds with
    | nil => exact List.mem_cons_self
    | cons β rest =>
      apply List.mem_cons_of_mem
      exact List.mem_map.mpr ⟨(β::rest,τ),ih (by simp),rfl⟩

theorem exactPrefix (σ : Ty) (domains : List Ty) (τ : Ty) :
    (domains,τ) ∈ fullPrefixes σ ↔ domains ≠ [] ∧ ArrowPrefix domains τ = σ := by
  refine ⟨forward σ domains τ,?_⟩
  rintro ⟨hn,rfl⟩
  exact backward domains τ hn

theorem positive (σ : Ty) : 0 < typeSize σ := by cases σ <;> simp [typeSize] <;> omega

theorem proper (σ : Ty) (domains : List Ty) (τ : Ty) (h : (domains,τ) ∈ fullPrefixes σ) :
    typeSize τ < typeSize σ ∧ ∀ ρ, ρ ∈ domains → typeSize ρ < typeSize σ := by
  induction σ generalizing domains τ with
  | ground => cases h
  | arrow α β iha ihb =>
    rcases List.mem_cons.mp h with h|h
    · cases h
      refine ⟨by simp only [typeSize]; have hp := positive α; omega,?_⟩
      intro ρ hρ
      have he : ρ=α := by simpa using hρ
      subst ρ; simp only [typeSize]; have hp := positive β; omega
    · obtain ⟨⟨ds,υ⟩,hd,he⟩ := List.mem_map.mp h
      cases he
      obtain ⟨ht,hds⟩ := ihb _ _ hd
      refine ⟨by simp only [typeSize]; omega,?_⟩
      intro ρ hρ
      rcases List.mem_cons.mp hρ with rfl|hρ
      · simp only [typeSize]; have hp := positive β; omega
      · have hh := hds ρ hρ; simp only [typeSize]; omega

theorem distinct (σ : Ty) : (fullPrefixes σ).Pairwise (· ≠ ·) := by
  induction σ with
  | ground => exact .nil
  | arrow α β iha ihb =>
    apply List.Pairwise.cons
    · intro p hp he
      obtain ⟨⟨ds,τ⟩,hd,heq⟩ := List.mem_map.mp hp
      cases heq
      have hn := ((exactPrefix β ds τ).mp hd).1
      have hh : ds=[] := (List.cons.inj (Prod.mk.inj he).1).2.symm
      exact hn hh
    · apply List.Pairwise.map _ (fun a b hab he => ?_) ihb
      apply hab
      exact Prod.ext (List.cons.inj (Prod.mk.inj he).1).2 (Prod.mk.inj he).2
end LogicLineages.PersistentMarking.FinitePrefixProof
