module
public import LogicLineages.ModelsAlgebra.Forests.RankedParseTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedParse.Proof

def reflMap (t : Term) : InducedMap t t where
  map := id
  injective := Function.injective_id
  adjacency := fun _ _ => Iff.rfl

def leftMap {s l r} (o : Operation) (f : InducedMap s l) :
    InducedMap s (.node o l r) where
  map := fun x => .inl (f.map x)
  injective := fun _ _ h => f.injective (Sum.inl.inj h)
  adjacency := f.adjacency

def rightMap {s l r} (o : Operation) (f : InducedMap s r) :
    InducedMap s (.node o l r) where
  map := fun x => .inr (f.map x)
  injective := fun _ _ h => f.injective (Sum.inr.inj h)
  adjacency := f.adjacency

def coupleMap {s₁ s₂ t₁ t₂} (o : Operation)
    (f : InducedMap s₁ t₁) (g : InducedMap s₂ t₂) :
    InducedMap (.node o s₁ s₂) (.node o t₁ t₂) where
  map := Sum.map f.map g.map
  injective := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (f.injective (Sum.inl.inj h))
      | inr y => cases h
    | inr x =>
      cases y with
      | inl y => cases h
      | inr y => exact congrArg Sum.inr (g.injective (Sum.inr.inj h))
  adjacency := by
    intro x y
    cases x <;> cases y
    · exact f.adjacency _ _
    · exact Iff.rfl
    · exact Iff.rfl
    · exact g.adjacency _ _

/-- The custom map record is exactly a standard induced graph embedding. -/
def asGraphEmbedding {s t} (f : InducedMap s t) : graph s ↪g graph t where
  toFun := f.map
  inj' := f.injective
  map_rel_iff' := f.adjacency _ _

theorem homeomorphicInduced : Targets.HomeomorphicInduced := by
  intro s t h
  induction h with
  | atom => exact ⟨reflMap .atom⟩
  | left o _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨leftMap o f⟩
  | right o _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨rightMap o f⟩
  | couple o _ _ ih₁ ih₂ =>
    obtain ⟨f⟩ := ih₁
    obtain ⟨g⟩ := ih₂
    exact ⟨coupleMap o f g⟩

theorem exactPruning : Targets.ExactPruning := by
  classical
  intro t
  induction t with
  | atom =>
    intro B hB
    refine ⟨.atom, .atom, reflMap .atom, ?_⟩
    intro y
    constructor
    · intro _
      obtain ⟨x, hx⟩ := hB
      cases x
      cases y
      exact hx
    · intro _
      exact ⟨y, rfl⟩
  | node o l r ihl ihr =>
    intro B hB
    by_cases hl : ∃ x : Leaf l, B (.inl x)
    · obtain ⟨s, hs, f, hf⟩ := ihl (fun x => B (.inl x)) hl
      by_cases hr : ∃ y : Leaf r, B (.inr y)
      · obtain ⟨u, hu, g, hg⟩ := ihr (fun y => B (.inr y)) hr
        refine ⟨.node o s u, .couple o hs hu, coupleMap o f g, ?_⟩
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
      · refine ⟨s, .left o hs, leftMap o f, ?_⟩
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
            exact False.elim (hr ⟨y, hy⟩)
    · have hr : ∃ y : Leaf r, B (.inr y) := by
        obtain ⟨x, hx⟩ := hB
        cases x with
        | inl x => exact False.elim (hl ⟨x, hx⟩)
        | inr x => exact ⟨x, hx⟩
      obtain ⟨u, hu, g, hg⟩ := ihr (fun y => B (.inr y)) hr
      refine ⟨u, .right o hu, rightMap o g, ?_⟩
      intro y
      cases y with
      | inl y =>
        constructor
        · rintro ⟨x, hx⟩
          cases hx
        · intro hy
          exact False.elim (hl ⟨y, hy⟩)
      | inr y =>
        constructor
        · rintro ⟨x, hx⟩
          exact (hg y).mp ⟨x, Sum.inr.inj hx⟩
        · intro hy
          obtain ⟨x, hx⟩ := (hg y).mpr hy
          exact ⟨x, congrArg Sum.inr hx⟩

end LogicLineages.ModelsAlgebra.Forests.RankedParse.Proof
