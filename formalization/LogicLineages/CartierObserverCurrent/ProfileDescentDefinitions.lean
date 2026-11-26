module
public import LogicLineages.CartierObserverCurrent.RationalCoverageDefinitions
public import LogicLineages.CartierObserverCurrent.NaturalityDefinitions
public import LogicLineages.CartierObserverCurrent.SplittingRootsProof

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.ProfileDescent
open SplittingRoots

/-- Chosen witness of the proved actual all-root squaring permutation. -/
noncomputable def rootSquare (d : Nat) : Equiv.Perm (Root d) :=
  Classical.choose (frobeniusRootPermutation d)

noncomputable def transport (d : Nat) (b : Root d → FieldAt d) (z : Root d) : FieldAt d :=
  b ((rootSquare d).symm z) ^ 2

def compatible (d : Nat) (b : Root d → FieldAt d) : Prop :=
  ∀ z : Root d, b (rootSquare d z) = b z ^ 2

noncomputable def extend (d : Nat) : RatFunc (ZMod 2) →+* RatFunc (FieldAt d) :=
  Naturality.rationalMap (algebraMap (ZMod 2) (FieldAt d))

/-- Independent base state, defined without profiles or reconstruction. -/
def baseState (d : Nat) (g : RatFunc (ZMod 2)) : Prop :=
  MixedProper.proper g ∧ (extend d g).denom ∣ RootInterpolation.rootProduct d
end LogicLineages.CartierObserverCurrent.ProfileDescent
