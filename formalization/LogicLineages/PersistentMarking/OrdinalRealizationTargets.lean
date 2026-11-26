module

public import Mathlib.SetTheory.Ordinal.Rank

@[expose] public section

namespace LogicLineages.PersistentMarking.OrdinalRealizationTargets

inductive FiniteType where
  | base
  | arrow (domain codomain : FiniteType)

abbrev CountableOrdinal := {o : Ordinal.{0} // Countable {β : Ordinal.{0} // β < o}}

def Value : FiniteType → Type 1
  | .base => CountableOrdinal
  | .arrow A D => Value A → Value D

def ValueLE : (A : FiniteType) → Value A → Value A → Prop
  | .base, α, β => α.val ≤ β.val
  | .arrow A D, f, g => ∀ x : Value A, ValueLE D (f x) (g x)

/-- Every coordinate uses the entire countable family. -/
def PointwiseSupremum {ι : Type 1} :
    (A : FiniteType) → (ι → Value A) → Value A → Prop
  | .base, f, α => α.val = ⨆ i, (f i).val
  | .arrow A D, f, g => ∀ x : Value A, PointwiseSupremum D (fun i => f i x) (g x)

structure TermStructure where
  term : FiniteType → Type
  below : (A : FiniteType) → term A → term A → Prop
  app : (A D : FiniteType) → term (.arrow A D) → term A → term D

def Realizes (terms : TermStructure) (wf : WellFounded (terms.below .base)) :
    (A : FiniteType) → terms.term A → Value A → Prop
  | .base, t, α => α.val ≤ (wf.apply t).rank
  | .arrow A D, t, f => ∀ (x : Value A) (u : terms.term A),
      Realizes terms wf A u x → Realizes terms wf D (terms.app A D t u) (f x)

def StrictFunctionSlot (terms : TermStructure) : Prop :=
  ∀ A D (s t : terms.term (.arrow A D)) (u : terms.term A),
    terms.below (.arrow A D) t s → terms.below D (terms.app A D t u) (terms.app A D s u)

def RealizationStrictBackward (terms : TermStructure) (wf : WellFounded (terms.below .base)) : Prop :=
  ∀ A (s t : terms.term A) (v : Value A),
    terms.below A t s → Realizes terms wf A t v → Realizes terms wf A s v

def RealizationDownward (terms : TermStructure) (wf : WellFounded (terms.below .base)) : Prop :=
  ∀ A (t : terms.term A) (v w : Value A),
    ValueLE A v w → Realizes terms wf A t w → Realizes terms wf A t v

def PointwiseSupremumExists : Prop :=
  ∀ A (ι : Type 1) [Countable ι] [Nonempty ι] (f : ι → Value A),
    ∃! v, PointwiseSupremum A f v

def RealizationCountableSupremum (terms : TermStructure) (wf : WellFounded (terms.below .base)) : Prop :=
  ∀ A (ι : Type 1) [Countable ι] [Nonempty ι]
    (t : terms.term A) (f : ι → Value A) (v : Value A),
    PointwiseSupremum A f v → (∀ i, Realizes terms wf A t (f i)) → Realizes terms wf A t v

end LogicLineages.PersistentMarking.OrdinalRealizationTargets
