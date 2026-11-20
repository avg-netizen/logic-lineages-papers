module

public import LogicLineages.PersistentMarking.OrdinalNativeIterationTargets
public import LogicLineages.PersistentMarking.OrdinalRealizationClosureProof

@[expose] public section

namespace LogicLineages.PersistentMarking.OrdinalNativeOrbitProof
open OrdinalRealizationTargets OrdinalRealizationClosureProof OrdinalNativeIterationTargets

private abbrev CountablePrefix (α : Ordinal.{0}) := Countable {β : Ordinal.{0} // β < α}

private theorem countablePrefixOfLE {α β : Ordinal.{0}} (h : α ≤ β) (count : CountablePrefix β) :
    CountablePrefix α :=
  Set.Countable.mono (s₁ := Set.Iio α) (s₂ := Set.Iio β)
    (fun _ hBelow => (show _ < α from hBelow).trans_le h) count

private theorem leAddOne (α : Ordinal.{0}) : α ≤ α + 1 :=
  (Order.lt_add_one_iff.mpr le_rfl).le

private def successorValue (A : FiniteType) (f : Value A → Value A) (α : Ordinal.{0})
    (previous : CountablePrefix α → Value A) (count : CountablePrefix (α + 1)) : Value A :=
  f (previous (countablePrefixOfLE (leAddOne α) count))

private noncomputable def limitValue (A : FiniteType) (α : Ordinal.{0}) (limit : Order.IsSuccLimit α)
    (previous : ∀ β < α, CountablePrefix β → Value A) (count : CountablePrefix α) : Value A :=
  letI : Countable {β : Ordinal.{0} // β < α} := count
  letI : Nonempty {β : Ordinal.{0} // β < α} := ⟨⟨0, limit.pos⟩⟩
  let family := fun β : {β : Ordinal.{0} // β < α} =>
    previous β.val β.property (countablePrefixOfLE β.property.le count)
  Classical.choose (exact_PointwiseSupremumExists A _ family).exists

private theorem limitValueSpec (A : FiniteType) (α : Ordinal.{0}) (limit : Order.IsSuccLimit α)
    (previous : ∀ β < α, CountablePrefix β → Value A) (count : CountablePrefix α) :
    PointwiseSupremum A
      (fun β : {β : Ordinal.{0} // β < α} =>
        previous β.val β.property (countablePrefixOfLE β.property.le count))
      (limitValue A α limit previous count) := by
  letI : Countable {β : Ordinal.{0} // β < α} := count
  letI : Nonempty {β : Ordinal.{0} // β < α} := ⟨⟨0, limit.pos⟩⟩
  exact Classical.choose_spec (exact_PointwiseSupremumExists A _ _).exists

private noncomputable def orbitValues (A : FiniteType) (f : Value A → Value A) (x : Value A)
    (α : Ordinal.{0}) : CountablePrefix α → Value A :=
  Ordinal.limitRecOn (motive := fun β => CountablePrefix β → Value A) α
    (fun _ => x) (successorValue A f) (limitValue A)

noncomputable def orbit (A : FiniteType) (f : Value A → Value A) (x : Value A)
    (α : CountableOrdinal) : Value A :=
  orbitValues A f x α.val α.property

theorem orbitEquations (A : FiniteType) (f : Value A → Value A) (x : Value A) :
    OrbitEquations A f x (orbit A f x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro α h
    rcases α with ⟨α, count⟩
    change α = 0 at h
    subst α
    simp only [orbit, orbitValues, Ordinal.limitRecOn_zero]
  · intro α β h
    rcases α with ⟨α, countα⟩
    rcases β with ⟨β, countβ⟩
    change β = α + 1 at h
    subst β
    rw [orbit, orbitValues, Ordinal.limitRecOn_add_one] <;> rfl
  · intro lim limit
    unfold orbit orbitValues
    rw [Ordinal.limitRecOn_limit lim.val _ _ _ limit]
    apply limitValueSpec

theorem exact_FullPrefixOrbitExists : FullPrefixOrbitExists := by
  intro A f x
  have equations := orbitEquations A f x
  refine ⟨orbit A f x, equations, ?_⟩
  intro g hg
  have same : ∀ α (count : CountablePrefix α), g ⟨α, count⟩ = orbit A f x ⟨α, count⟩ := by
    intro α
    induction α using Ordinal.limitRecOn with
    | zero =>
      intro count
      rw [hg.1 ⟨0, count⟩ rfl, equations.1 ⟨0, count⟩ rfl]
    | add_one β ih =>
      intro count
      let countβ := countablePrefixOfLE (leAddOne β) count
      rw [hg.2.1 ⟨β, countβ⟩ ⟨β + 1, count⟩ rfl,
          equations.2.1 ⟨β, countβ⟩ ⟨β + 1, count⟩ rfl, ih countβ]
    | limit α hlim ih =>
      intro count
      let lim : CountableOrdinal := ⟨α, count⟩
      letI : Countable (EarlierStages lim) := count
      letI : Nonempty (EarlierStages lim) := ⟨⟨0, hlim.pos⟩⟩
      have sameEarlier :
          (fun β : EarlierStages lim => g (earlierStage lim β)) =
            (fun β : EarlierStages lim => orbit A f x (earlierStage lim β)) :=
        funext fun β => ih β.val β.property (earlierStage lim β).property
      have gSup := hg.2.2 lim hlim
      rw [sameEarlier] at gSup
      exact (exact_PointwiseSupremumExists A _ _).unique gSup (equations.2.2 lim hlim)
  funext α
  exact same α.val α.property

#print axioms exact_FullPrefixOrbitExists

end LogicLineages.PersistentMarking.OrdinalNativeOrbitProof
