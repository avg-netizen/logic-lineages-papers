module

public import LogicLineages.PersistentMarking.OrdinalRealizationTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.OrdinalNativeIterationTargets
open OrdinalRealizationTargets

abbrev EarlierStages (α : CountableOrdinal) := {β : Ordinal.{0} // β < α.val}

def earlierStage (α : CountableOrdinal) (β : EarlierStages α) : CountableOrdinal :=
  ⟨β.val, Set.Countable.mono (s₁ := Set.Iio β.val) (s₂ := Set.Iio α.val)
    (fun _ h => h.trans β.property) α.property⟩

/-- Convention (I) uses the entire strict initial segment at a limit. -/
def OrbitEquations (A : FiniteType) (f : Value A → Value A) (x : Value A)
    (orbit : CountableOrdinal → Value A) : Prop :=
  (∀ α, α.val = 0 → orbit α = x) ∧
  (∀ α β, β.val = α.val + 1 → orbit β = f (orbit α)) ∧
  (∀ λo, IsSuccLimit λo.val →
    PointwiseSupremum A (fun β : EarlierStages λo => orbit (earlierStage λo β)) (orbit λo))

def FullPrefixOrbitExists : Prop :=
  ∀ A (f : Value A → Value A) (x : Value A),
    ∃! orbit : CountableOrdinal → Value A, OrbitEquations A f x orbit

abbrev IndexedCarrier (terms : TermStructure) :=
  (A : FiniteType) → terms.term (.arrow A A) → terms.term A → terms.term .base → terms.term A

def IndexedCarrierEdges (terms : TermStructure) (W : IndexedCarrier terms) : Prop :=
  ∀ A P U i,
    terms.below A U (W A P U i) ∧
    ∀ j, terms.below .base j i →
      terms.below A (W A P U j) (W A P U i) ∧
      terms.below A (terms.app A A P (W A P U j)) (W A P U i)

def IndexedCarrierRealizesOrbit (terms : TermStructure) (wf : WellFounded (terms.below .base))
    (W : IndexedCarrier terms) : Prop :=
  ∀ A (f : Value A → Value A) (x : Value A) (orbit : CountableOrdinal → Value A),
    OrbitEquations A f x orbit →
    ∀ P U i, Realizes terms wf (.arrow A A) P f → Realizes terms wf A U x →
    ∀ β, β.val ≤ (wf.apply i).rank → Realizes terms wf A (W A P U i) (orbit β)

end LogicLineages.PersistentMarking.OrdinalNativeIterationTargets
