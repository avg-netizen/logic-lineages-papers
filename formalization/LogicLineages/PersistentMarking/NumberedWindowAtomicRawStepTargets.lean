module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepTargets
open NumberedWindowAtomicRawStep
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowAnnotationAlgorithm (annotations)
open NumberedWindowRawContextAlgorithm (next)
open NumberedWindowConcreteCheckers (root step)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings admitted)

def ExactAtomicRawFields : Prop :=
  (∀ t n, unpackNode (freeRaw t n) = some (0,[t,n]) ∧ (annotations (freeRaw t n)).1 = t) ∧
  (∀ t, unpackNode (bottomRaw t) = some (3,[t]) ∧ (annotations (bottomRaw t)).1 = t) ∧
  (∀ t n u, freeRaw t n ≠ bottomRaw u) ∧
  unpackNode bottomRoot = some (7,[])

/-- Genuine original concrete root dispatch. Every raw certificate is
allowed as input; only the accepted branch is classified. -/
def ExactConcreteAtomicRoot : Prop :=
  (∀ (xs : Entries) (s : Settings) t n witness y,
    root xs s (freeRaw t n) witness y = true → y = bottomRaw t ∧ witness = bottomRoot) ∧
  (∀ (xs : Entries) (s : Settings) t witness y,
    root xs s (bottomRaw t) witness y = false)

/-- No proper context frame descends into either literal raw atom.
No admission type or legal witness restriction has been added. -/
def ExactAtomicNoContextDescent : Prop :=
  (∀ tag ws t n y, next tag ws (freeRaw t n) y = none) ∧
  (∀ tag ws t y, next tag ws (bottomRaw t) y = none)

/-- Actual original bounded iteration, syntax and window checks.
The requested type is independent of the stored raw annotation t.
The result is classified only on genuine accepted free steps. -/
def ExactConcreteAtomicRawStep : Prop :=
  (∀ (xs : Entries) (s : Settings) (Γ : List Nat) requested t n witness y,
    step xs s Γ requested (freeRaw t n) witness y = true →
      y = bottomRaw t ∧ admitted s Γ requested (bottomRaw t) = true) ∧
  (∀ (xs : Entries) (s : Settings) (Γ : List Nat) requested t witness y,
    step xs s Γ requested (bottomRaw t) witness y = false)

end LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepTargets
