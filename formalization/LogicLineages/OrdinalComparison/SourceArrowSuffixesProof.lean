module
public import LogicLineages.OrdinalComparison.SourceArrowSuffixesTargets
public import LogicLineages.OrdinalComparison.SourceTypesProofs
public import Mathlib.Data.List.Nodup
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceArrowSuffixesProof
open SourceArrowSuffixes SourceArrowSuffixesTargets SourceSpecialApplication

theorem exactArrowSuffixEnumeration : ExactArrowSuffixEnumeration := by
  intro σ
  induction σ with
  | ground =>
    intro args τ
    cases args <;> simp [arrowSuffixes, arrows]
  | arrow α β ihα ihβ =>
    intro args τ
    constructor
    · intro hm
      rcases List.mem_cons.mp hm with he | hm
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact ⟨by simp, rfl⟩
      · obtain ⟨⟨xs, r⟩, hp, he⟩ := List.mem_map.mp hm
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        have hh := (ihβ xs r).mp hp
        exact ⟨by simp, by simp only [arrows, hh.2]⟩
    · rintro ⟨hne, he⟩
      cases args with
      | nil => exact False.elim (hne rfl)
      | cons ρ rest =>
        have hh : Ty.arrow ρ (arrows rest τ) = Ty.arrow α β := he
        obtain ⟨rfl, hr⟩ := Ty.arrow.inj hh
        cases rest with
        | nil =>
          have ht : τ = β := hr
          subst τ
          exact List.mem_cons_self
        | cons υ rest =>
          exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(υ :: rest, τ),
            (ihβ (υ :: rest) τ).mpr ⟨by simp, hr⟩, rfl⟩)

private theorem result_subtype (args : List Ty) (τ : Ty) : τ ∈ (arrows args τ).subtypes := by
  induction args with
  | nil => exact Ty.mem_subtypes_self τ
  | cons σ args ih =>
    exact List.mem_cons_of_mem _ (List.mem_append_right _ ih)

private theorem argument_subtype (args : List Ty) (τ : Ty) :
    ∀ ρ ∈ args, ρ ∈ (arrows args τ).subtypes := by
  induction args with
  | nil => simp
  | cons σ args ih =>
    intro ρ hρ
    rcases List.mem_cons.mp hρ with rfl | hρ
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (Ty.mem_subtypes_self ρ))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ih ρ hρ))

theorem arrowSuffixSubtypes : ArrowSuffixSubtypes := by
  intro σ args τ hm
  have he := (exactArrowSuffixEnumeration σ args τ).mp hm
  rw [← he.2]
  exact ⟨result_subtype args τ, argument_subtype args τ⟩

private theorem result_size_le (args : List Ty) (τ : Ty) :
    typeSize τ ≤ typeSize (arrows args τ) := by
  induction args with
  | nil => exact Nat.le_refl _
  | cons σ args ih =>
    change typeSize τ ≤ 1 + typeSize σ + typeSize (arrows args τ)
    omega

private theorem result_size_lt (args : List Ty) (τ : Ty) (h : args ≠ []) :
    typeSize τ < typeSize (arrows args τ) := by
  cases args with
  | nil => exact False.elim (h rfl)
  | cons σ args =>
    have hh := result_size_le args τ
    change typeSize τ < 1 + typeSize σ + typeSize (arrows args τ)
    omega

private theorem argument_size (args : List Ty) (τ : Ty) :
    ∀ ρ ∈ args, typeSize ρ < typeSize (arrows args τ) := by
  induction args with
  | nil => simp
  | cons σ args ih =>
    intro ρ hρ
    rcases List.mem_cons.mp hρ with rfl | hρ
    · change typeSize ρ < 1 + typeSize ρ + typeSize (arrows args τ)
      omega
    · have hh := ih ρ hρ
      change typeSize ρ < 1 + typeSize σ + typeSize (arrows args τ)
      omega

theorem arrowSuffixStrictSize : ArrowSuffixStrictSize := by
  intro σ args τ hm
  have he := (exactArrowSuffixEnumeration σ args τ).mp hm
  rw [← he.2]
  exact ⟨result_size_lt args τ he.1, argument_size args τ⟩

theorem arrowSuffixNoDuplicates : ArrowSuffixNoDuplicates := by
  intro σ
  induction σ with
  | ground => exact List.nodup_nil
  | arrow α β ihα ihβ =>
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      obtain ⟨⟨args, τ⟩, hp, he⟩ := List.mem_map.mp hm
      have ha : α :: args = [α] := congrArg Prod.fst he
      have hempty : args = [] := (List.cons.inj ha).2
      exact ((exactArrowSuffixEnumeration β args τ).mp hp).1 hempty
    · apply List.Nodup.map ?_ ihβ
      intro p q he
      rcases p with ⟨ps, pτ⟩
      rcases q with ⟨qs, qτ⟩
      obtain ⟨ha, hr⟩ := Prod.mk.inj he
      exact Prod.ext (List.cons.inj ha).2 hr

end LogicLineages.OrdinalComparison.Source.SourceArrowSuffixesProof
