import LogicLineages.PersistentMarking.NativeIteratorStrictTargets
import LogicLineages.PersistentMarking.NumberedWindowOrdinaryTranslation
import LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCode

namespace LogicLineages.PersistentMarking.NativeSyntaxCountabilityTargets
open NumberedWindowSyntax NumberedWindowOrdinaryTranslation
open NumberedWindowArithmeticTermCode NativeIteratorStrictTargets

mutual
/-- The partial inverse on the image of the literal ordinary translation. -/
def readOrdinary : NTerm → Option Spine.Expr
  | .free σ x => some (.free σ x)
  | .bound σ i => some (.bound σ i)
  | .lam σ body => (readOrdinary body).map (.lam σ)
  | .ordinary f bs => (readOrdinaryArgs bs).map (.head f)
  | .bottom _ | .numbered _ _ _ _ _ | .auxApp _ _ _ _ => none
def readOrdinaryArgs : NArgs → Option Spine.Args
  | .nil => some .nil
  | .cons a tail => do
    let q ← readOrdinary a
    let qs ← readOrdinaryArgs tail
    pure (.cons q qs)
end

def OrdinaryLiteralRoundtrip : Prop :=
  (∀ q Q, tr q = some Q → readOrdinary Q = some q) ∧
  (∀ bs As, trArgs bs = some As → readOrdinaryArgs As = some bs)

def nativeCode {S τ} (q : ClosedNativeTerm S τ) : Nat :=
  ((tr q.val).map encodeTerm).getD 0

/-- Countability of the actual same-type closed native syntax via its literal code. -/
def ClosedNativeCountability : Prop :=
  ∀ S τ, Function.Injective (@nativeCode S τ)

end LogicLineages.PersistentMarking.NativeSyntaxCountabilityTargets
