import LogicLineages.PersistentMarking.ProtectedSpineDecisionTargets
import LogicLineages.PersistentMarking.StablePairTargets
import LogicLineages.PersistentMarking.NumberedWindowExternalWellFoundedTargets
import LogicLineages.PersistentMarking.NativeOrientationTargets
import LogicLineages.PersistentMarking.RankedRestrictionTargets

namespace LogicLineages.PersistentMarking.PrincipalNonOrdinalTargets
open Spine StablePairTargets

/-- Item (1), only the two confined bits of the actual decision procedure. -/
def Decision : Prop :=
  ∀ S s t σ τ, PaperTerm S s σ → Ordinary s → PaperTerm S t τ → Ordinary t →
    ((ProtectedSpineDecisionTargets.confinedBits S s t).1 = true ↔ ConfinedPair.Weak S s t) ∧
    ((ProtectedSpineDecisionTargets.confinedBits S s t).2 = true ↔ ConfinedPair.Strict S s t)

/-- Item (2), including strict well-foundedness in the descending direction. -/
def OrderLaws : Prop :=
  WeakReflexive ∧ WeakTransitive ∧ StrictTransitive ∧
    NumberedWindowExternalWellFoundedTargets.ConfinedStrictWellFounded ∧
    StrictIncluded ∧ WeakStrict ∧ StrictWeak

/-- Item (3), for the original typed contexts and capture-avoiding
substitution on ordinary terms. -/
def Structural : Prop :=
  WeakContext ∧ StrictContext ∧ WeakSubstitution ∧ StrictSubstitution

/-- Item (4), the original beta, case and recursor reductions with
their context/substitution instances. -/
def Orientation : Prop := NativeOrientationTargets.FullOrientation

/-- Item (5), both directions of the strict multiset-RPO restriction. -/
def Ranked : Prop :=
  ∀ S s t, RankedRestrictionTargets.Term S s → RankedRestrictionTargets.Term S t →
    (ConfinedPair.Strict S s t ↔ RankedRestrictionTargets.RPO S s t)

def PrincipalNonOrdinal : Prop := Decision ∧ OrderLaws ∧ Structural ∧ Orientation ∧ Ranked

end LogicLineages.PersistentMarking.PrincipalNonOrdinalTargets
