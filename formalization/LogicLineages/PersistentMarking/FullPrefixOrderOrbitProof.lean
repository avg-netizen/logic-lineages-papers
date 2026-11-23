import Mathlib.Order.Bounds.Defs

namespace LogicLineages.PersistentMarking.FullPrefixOrderOrbitProof

variable {I V T : Type*}

/-- Genuine no-predecessor and greatest-predecessor tests on the supplied
strict index order, not tags that may ignore some of a limit's prefix. -/
def First (r : I → I → Prop) (i : I) : Prop :=
  ∀ j, ¬ r j i

def SuccessorOf (r : I → I → Prop) (j i : I) : Prop :=
  r j i ∧ ∀ k, r k i → k = j ∨ r k j

def Limit (r : I → I → Prop) (i : I) : Prop :=
  (∃ j, r j i) ∧ ¬ ∃ j, SuccessorOf r j i

def PrefixValues (r : I → I → Prop) (values : I → V) (i : I) : Set V :=
  { x | ∃ j, r j i ∧ values j = x }

structure FullPrefixEquations [LE V] (r : I → I → Prop)
    (f : V → V) (x : V) (orbit : I → V) : Prop where
  firstValue : ∀ i, First r i → orbit i = x
  nextValue : ∀ j i, SuccessorOf r j i → orbit i = f (orbit j)
  limitValue : ∀ i, Limit r i → IsLUB (PrefixValues r orbit i) (orbit i)

structure CarrierEdges (r : I → I → Prop) (strict : T → T → Prop)
    (carrier : I → T) (push : T → T) (seed : T) : Prop where
  seedBelow : ∀ i, strict seed (carrier i)
  earlierBelow : ∀ j i, r j i → strict (carrier j) (carrier i)
  pushedEarlierBelow : ∀ j i, r j i → strict (push (carrier j)) (carrier i)

/-- The limit law is a separate genuine closure premise about the
realization relation on the same fixed term, under all values of a limit
prefix. It does not say that any particular orbit is already realized. -/
structure RealizationLaws [LE V] (r : I → I → Prop) (strict : T → T → Prop)
    (push : T → T) (f : V → V) (realizes : T → V → Prop) : Prop where
  backward : ∀ {u t z}, strict u t → realizes u z → realizes t z
  action : ∀ {u z}, realizes u z → realizes (push u) (f z)
  fullPrefixSup : ∀ (t : T) (i : I) (values : I → V) (z : V), Limit r i →
    IsLUB (PrefixValues r values i) z →
    (∀ j, r j i → realizes t (values j)) → realizes t z

theorem exact_FullPrefixCarrierOrbit [LE V]
    {r : I → I → Prop} {strict : T → T → Prop} {carrier : I → T}
    {push : T → T} {seed : T} {f : V → V} {x : V} {orbit : I → V} {realizes : T → V → Prop}
    (wf : WellFounded r)
    (equations : FullPrefixEquations r f x orbit)
    (edges : CarrierEdges r strict carrier push seed)
    (laws : RealizationLaws r strict push f realizes)
    (seedValue : realizes seed x) :
    ∀ i, realizes (carrier i) (orbit i) := by
  intro i
  induction i using wf.induction with
  | h i ih =>
    classical
    by_cases inhabited : ∃ j, r j i
    · by_cases last : ∃ j, SuccessorOf r j i
      · obtain ⟨j,next⟩ := last
        rw [equations.nextValue j i next]
        exact laws.backward (edges.pushedEarlierBelow j i next.1) (laws.action (ih j next.1))
      · have limit : Limit r i := ⟨inhabited,last⟩
        apply laws.fullPrefixSup (carrier i) i orbit (orbit i) limit (equations.limitValue i limit)
        intro j earlier
        exact laws.backward (edges.earlierBelow j i earlier) (ih j earlier)
    · have first : First r i := fun j earlier => inhabited ⟨j,earlier⟩
      rw [equations.firstValue i first]
      exact laws.backward (edges.seedBelow i) seedValue

/-- Each current carrier realizes its own orbit point and every point in its
actual strict prefix, with no monotonicity hypothesis on f or on the orbit. -/
theorem exact_FullPrefixCarrierAllApproached [LE V]
    {r : I → I → Prop} {strict : T → T → Prop} {carrier : I → T}
    {push : T → T} {seed : T} {f : V → V} {x : V} {orbit : I → V} {realizes : T → V → Prop}
    (wf : WellFounded r)
    (equations : FullPrefixEquations r f x orbit)
    (edges : CarrierEdges r strict carrier push seed)
    (laws : RealizationLaws r strict push f realizes)
    (seedValue : realizes seed x) :
    ∀ i j, (j = i ∨ r j i) → realizes (carrier i) (orbit j) := by
  have same := exact_FullPrefixCarrierOrbit wf equations edges laws seedValue
  intro i j atOrBefore
  rcases atOrBefore with eq | earlier
  · rw [eq]
    exact same i
  · exact laws.backward (edges.earlierBelow j i earlier) (same j)

#print axioms exact_FullPrefixCarrierOrbit
#print axioms exact_FullPrefixCarrierAllApproached

end LogicLineages.PersistentMarking.FullPrefixOrderOrbitProof
