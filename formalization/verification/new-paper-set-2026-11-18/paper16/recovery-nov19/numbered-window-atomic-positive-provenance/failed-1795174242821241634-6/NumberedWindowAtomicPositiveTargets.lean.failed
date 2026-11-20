module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowAtomicPositiveTargets
open NumberedWindowAtomicRawStep
open NumberedWindowFieldAlgorithm (packNode unpack)
open NumberedWindowAddressAlgorithm (addressView contextView typeBit)
open NumberedWindowConcreteCheckers (step positive)
open NumberedWindowScalarAlgorithm (Settings admitted least scalar)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowPositivePathAlgorithm (advance)

def packedAddress (context result least : Nat) : Nat := packNode 3 [context,result,least]
def freeAddress (context t n : Nat) : Nat := packedAddress context t (freeRaw t n)
def bottomAddress (context t : Nat) : Nat := packedAddress context t (bottomRaw t)

/-- Even when the literal shell has the right tag and arity, the actual
original context and result-type option validations remain. No check
on the raw term payload is added to the original address decoder. -/
def ExactLiteralAtomicAddressView : Prop :=
  ∀ context result payload,
    addressView (packedAddress context result payload) =
      (contextView context).bind (fun Γ => if typeBit result then some (Γ,result,payload) else none)

/-- A genuine original first-hop callback and both actual least tests.
For arbitrary original raw contexts, requested types and hop codes,
the successful free result is the same admitted bottom; no bottom
can start a successful subsequent hop. -/
def ExactConcreteAtomicAdvance : Prop :=
  (∀ (xs : Entries) (s : Settings) (Γ : List Nat) requested t n code y,
    advance (step xs s Γ requested) (least s Γ requested) (some (freeRaw t n)) code = some y →
      y = bottomRaw t ∧ admitted s Γ requested y = true ∧ least s Γ requested y = some y) ∧
  (∀ (xs : Entries) (s : Settings) (Γ : List Nat) requested t code,
    advance (step xs s Γ requested) (least s Γ requested) (some (bottomRaw t)) code = none)

/-- The supplied positive certificate's own decoded raw list is a
singleton, not a newly chosen witness. An accepted free hop cannot
continue from its same-type bottom result. -/
def ExactConcreteAtomicPositivePath : Prop :=
  (∀ (xs : Entries) (s : Settings) (Γ : List Nat) requested t n witness y,
    NumberedWindowPositivePathAlgorithm.positive (step xs s) (least s) Γ requested
      (freeRaw t n) witness y = true →
    y = bottomRaw t ∧ admitted s Γ requested y = true ∧ least s Γ requested y = some y ∧
    ∃ code, unpack witness = some [code] ∧
      advance (step xs s Γ requested) (least s Γ requested) (some (freeRaw t n)) code = some y) ∧
  (∀ (xs : Entries) (s : Settings) (Γ : List Nat) requested t witness y,
    NumberedWindowPositivePathAlgorithm.positive (step xs s) (least s) Γ requested
      (bottomRaw t) witness y = false)

/-- Full original address positive relation, not a direct-edge check.
The output uses the very same raw packed context/type, and its actual
scalar carrier bit holds. Arbitrary malformed represented contexts
remain part of this accepted-implication domain. -/
def ExactConcreteAtomicAddressPositive : Prop :=
  (∀ (xs : Entries) (s : Settings) context t n witness y,
    positive xs s (freeAddress context t n) witness y = true →
      y = bottomAddress context t ∧ scalar s y = true) ∧
  (∀ (xs : Entries) (s : Settings) context t witness y,
    positive xs s (bottomAddress context t) witness y = false)

end LogicLineages.PersistentMarking.NumberedWindowAtomicPositiveTargets
