module
public import LogicLineages.ModelsAlgebra.Forests.RankedPruneAlgorithmTargets
public import LogicLineages.ModelsAlgebra.Forests.RankedParseProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedPruneAlgorithm.Proof
open RankedParse

theorem noneExact : Targets.NoneExact := by
  intro t
  induction t with
  | atom =>
    intro B
    cases hb : B () with
    | false =>
      constructor
      · intro _ x
        cases x
        exact hb
      · intro _
        simp [prune, hb]
    | true =>
      constructor
      · intro h
        simp [prune, hb] at h
      · intro h
        have hh := h ()
        simp [hb] at hh
  | node o l r ihl ihr =>
    intro B
    change _ ↔ ∀ x : Sum (Leaf l) (Leaf r), B x = false
    have hforall : (∀ x : Sum (Leaf l) (Leaf r), B x = false) ↔
        (∀ x, B (.inl x) = false) ∧ (∀ y, B (.inr y) = false) := by
      constructor
      · intro h
        exact ⟨fun x => h (.inl x), fun y => h (.inr y)⟩
      · rintro ⟨hl, hr⟩ x
        cases x with
        | inl x => exact hl x
        | inr y => exact hr y
    rw [hforall, ← ihl (fun x => B (.inl x)), ← ihr (fun x => B (.inr x))]
    cases hl : prune l (fun x => B (.inl x)) <;>
      cases hr : prune r (fun x => B (.inr x)) <;> simp [prune, hl, hr]

theorem someExact : Targets.SomeExact := by
  intro t
  induction t with
  | atom =>
    intro B s h
    cases hb : B () with
    | false => simp [prune, hb] at h
    | true =>
      have he : Term.atom = s := by simpa [prune, hb] using h
      subst s
      refine ⟨.atom, RankedParse.Proof.reflMap .atom, ?_⟩
      intro y
      cases y
      constructor
      · intro _
        exact hb
      · intro _
        exact ⟨(), rfl⟩
  | node o l r ihl ihr =>
    intro B s h
    cases hl : prune l (fun x => B (.inl x)) with
    | none =>
      cases hr : prune r (fun x => B (.inr x)) with
      | none => simp [prune, hl, hr] at h
      | some u =>
        have he : u = s := by simpa [prune, hl, hr] using h
        subst s
        obtain ⟨hu, g, hg⟩ := ihr (fun x => B (.inr x)) u hr
        refine ⟨.right o hu, RankedParse.Proof.rightMap o g, ?_⟩
        intro y
        cases y with
        | inl y =>
          constructor
          · rintro ⟨x, hx⟩
            cases hx
          · intro hy
            have hf := (noneExact l (fun x => B (.inl x))).mp hl y
            simp [hf] at hy
        | inr y =>
          constructor
          · rintro ⟨x, hx⟩
            exact (hg y).mp ⟨x, Sum.inr.inj hx⟩
          · intro hy
            obtain ⟨x, hx⟩ := (hg y).mpr hy
            exact ⟨x, congrArg Sum.inr hx⟩
    | some u =>
      obtain ⟨hu, f, hf⟩ := ihl (fun x => B (.inl x)) u hl
      cases hr : prune r (fun x => B (.inr x)) with
      | none =>
        have he : u = s := by simpa [prune, hl, hr] using h
        subst s
        refine ⟨.left o hu, RankedParse.Proof.leftMap o f, ?_⟩
        intro y
        cases y with
        | inl y =>
          constructor
          · rintro ⟨x, hx⟩
            exact (hf y).mp ⟨x, Sum.inl.inj hx⟩
          · intro hy
            obtain ⟨x, hx⟩ := (hf y).mpr hy
            exact ⟨x, congrArg Sum.inl hx⟩
        | inr y =>
          constructor
          · rintro ⟨x, hx⟩
            cases hx
          · intro hy
            have hf := (noneExact r (fun x => B (.inr x))).mp hr y
            simp [hf] at hy
      | some v =>
        have he : Term.node o u v = s := by simpa [prune, hl, hr] using h
        subst s
        obtain ⟨hv, g, hg⟩ := ihr (fun x => B (.inr x)) v hr
        refine ⟨.couple o hu hv, RankedParse.Proof.coupleMap o f g, ?_⟩
        intro y
        cases y with
        | inl y =>
          constructor
          · rintro ⟨x, hx⟩
            cases x with
            | inl x => exact (hf y).mp ⟨x, Sum.inl.inj hx⟩
            | inr x => cases hx
          · intro hy
            obtain ⟨x, hx⟩ := (hf y).mpr hy
            exact ⟨.inl x, congrArg Sum.inl hx⟩
        | inr y =>
          constructor
          · rintro ⟨x, hx⟩
            cases x with
            | inl x => cases hx
            | inr x => exact (hg y).mp ⟨x, Sum.inr.inj hx⟩
          · intro hy
            obtain ⟨x, hx⟩ := (hg y).mpr hy
            exact ⟨.inr x, congrArg Sum.inr hx⟩

end LogicLineages.ModelsAlgebra.Forests.RankedPruneAlgorithm.Proof
