module

public import LogicLineages.ModelsAlgebra.PGroups.BoundedExtensionTargets
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Group.Prod

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

def groupBoundedCyclicRetraction : Prop :=
  ∀ (n : ℕ) [NeZero n] (G : Type) [AddCommGroup G], (∀ x : G, n • x = 0) →
    ∀ (i : ZMod n →+ G), Function.Injective i →
      ∃ r : G →+ ZMod n, ∀ a : ZMod n, r (i a) = a

/-- Pure algebra of actual supplied section/retraction maps. The source
existence theorem below pays these maps instead of assuming them. -/
def groupRetractionKernelProduct : Prop :=
  ∀ (A G : Type) [AddCommGroup A] [AddCommGroup G]
    (i : A →+ G) (r : G →+ A), (∀ a, r (i a) = a) →
      Nonempty (G ≃+ (A × r.ker))

/-- Genuine maximal-order cyclic splitting existence, including n=1.
No projection, decomposition or categoricity property is an input. -/
def groupMaximalCyclicSplitting : Prop :=
  ∀ (n : ℕ) [NeZero n] (G : Type) [AddCommGroup G], (∀ x : G, n • x = 0) →
    ∀ y : G, addOrderOf y = n → ∃ r : G →+ ZMod n,
      r y = 1 ∧ Nonempty (G ≃+ (ZMod n × r.ker))

end LogicLineages.ModelsAlgebra.PGroups.Targets
