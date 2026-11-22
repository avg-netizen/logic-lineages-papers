import LogicLineages.PersistentMarking.NumberedWindowArithmeticExchangeAtomsTargets

namespace LogicLineages.PersistentMarking.NumberedWindowFixedExchangeSymmetryTargets

open NumberedWindowArithmeticExchangeAtomsTargets (pairs)
open NumberedWindowExchangeAtoms (allowed)

/-- The actual finite fixed-signature head table is symmetric as a
membership test, including at arbitrary raw numeric arguments. -/
def ExactFixedHeadPairsSymmetry : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (a b : Nat),
    allowed (pairs S K) a b = allowed (pairs S K) b a

end LogicLineages.PersistentMarking.NumberedWindowFixedExchangeSymmetryTargets
