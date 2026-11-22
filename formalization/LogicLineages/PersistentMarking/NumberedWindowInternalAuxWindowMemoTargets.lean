module

public import LogicLineages.PersistentMarking.NumberedWindowAuxExchangeLiftTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParser

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowMemoTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalRawListRecursion (lookup)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowAddressAlgorithm (typeBit)
open NumberedWindowAnnotationAlgorithm (annotations arrow)
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowInternalSparseTypedRawTargets (packedWindow)
open NumberedWindowInternalSparseFieldParser (scratchRow)

def typeGuard (s : Settings) (ty : Nat) : Bool := typeBit ty && s.window.1.contains ty

def intrinsicType (n : Nat) : Nat := (annotations n).1

/-- The row reports the literal own type if the original packed window
accepts at that type; zero is the original rejection code. -/
def intrinsicWindow (s : Settings) (ctx raw : Nat) : Nat :=
  let ty := intrinsicType raw
  if packedWindow s ctx ty raw then ty+1 else 0

def ExactPackedIntrinsicProjection : Prop := ∀ (s : Settings) ctx ty raw,
  packedWindow s ctx ty raw = (intrinsicWindow s ctx raw == ty+1)

/-- The actual same-context positive auxiliary branch and its exact
original optional-type result. All raw context and field inputs are covered. -/
def ExactIntrinsicAuxWindow : Prop := ∀ (s : Settings) ctx dom cod fn arg,
  intrinsicWindow s ctx (auxRaw dom cod fn arg) =
    if typeGuard s dom && typeGuard s cod &&
      (intrinsicWindow s ctx fn == arrow dom cod + 1) && (intrinsicWindow s ctx arg == dom+1)
    then cod+1 else 0

def IntrinsicWindowCalibrated (s : Settings) (base : Program 2) : Prop :=
  ∀ ctx raw, evaluate base (ctx ::ᵥ raw ::ᵥ nil) = intrinsicWindow s ctx raw

/-- The auxiliary shortcut can add a positive result only with both
actual child reports. All other cases call the unchanged base. -/
def rowValue (s : Settings) (base : Program 2) (i old ctx : Nat) : Nat :=
  let fallback := evaluate base (ctx ::ᵥ (i+1) ::ᵥ nil)
  match unpackNode (i+1) with
  | some (6,[dom,cod,fn,arg]) =>
    if fn < i+1 ∧ arg < i+1 ∧ typeGuard s dom = true ∧ typeGuard s cod = true ∧
        evaluate lookup ((i-fn) ::ᵥ old ::ᵥ nil) = arrow dom cod + 1 ∧
        evaluate lookup ((i-arg) ::ᵥ old ::ᵥ nil) = dom+1 then cod+1 else fallback
  | _ => fallback

def WindowStepCalibrated (s : Settings) (base : Program 2) (R : Program 4) : Prop :=
  ∀ i old ctx, evaluate R (i ::ᵥ old ::ᵥ ctx ::ᵥ 0 ::ᵥ nil) = rowValue s base i old ctx

def selectedIntrinsic (R : Program 4) : Program 2 :=
  .composition (scratchRow (constantZero 2) R)
    (Fin.cons (.projection 1) (Fin.cons (.projection 0) (Fin.cons (constantZero 2) Fin.elim0)))

def ExactIntrinsicMemoCalibration : Prop := ∀ (s : Settings) (base : Program 2) (R : Program 4),
  IntrinsicWindowCalibrated s base → WindowStepCalibrated s base R → IntrinsicWindowCalibrated s (selectedIntrinsic R)

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowMemoTargets
