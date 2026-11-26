import LogicLineages.PersistentMarking.NumberedWindowOuterShapeTargets
import LogicLineages.PersistentMarking.NumberedWindowDirectClassAddressTargets

namespace LogicLineages.PersistentMarking.NumberedWindowAtomicAddressTargets
open Spine NumberedWindowOuterShape NumberedWindowArithmeticScalarTargets
open NumberedWindowDirectClassAddressTargets NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticClassAddress

/-- No supplied direct class edge exits an actual canonical bottom. -/
def NoBottomDirectAddress : Prop :=
  ∀ (S : Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∀ source certificate target,
      outerShape (fixed S K) source = some 3 →
      literalDirect S K source certificate target = false

/-- Any genuine direct reduct of a canonical free or bound occurrence is
the literal canonical bottom of the same finite context and result type. -/
def ExactVariableDirectAddress : Prop :=
  ∀ (S : Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∀ source certificate target tag,
      (tag = 0 ∨ tag = 1) → outerShape (fixed S K) source = some tag →
      literalDirect S K source certificate target = true →
        ∃ (Γ : List Ty) (τ : Ty) (i : Nat),
          encodeAddress ⟨Γ,τ,i⟩ = source ∧
          target = encodeAddress ⟨Γ,τ,encodeTerm (.bottom τ)⟩ ∧
          outerShape (fixed S K) target = some 3

end LogicLineages.PersistentMarking.NumberedWindowAtomicAddressTargets
