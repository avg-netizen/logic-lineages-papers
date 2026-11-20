module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionTargets
open NumberedWindowAtomicApplicationTargets
open NumberedWindowAtomicRawStep (freeRaw bottomRaw bottomRoot)
open NumberedWindowFieldAlgorithm (unpack unpackNode)
open NumberedWindowConcreteCheckers (root step)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings admitted least)
open NumberedWindowRawContextAlgorithm (Frame next)
open NumberedWindowPositivePathAlgorithm (advance hopView)

/-- For the actual original root dispatcher, a bare-atomic function
cannot beta; the only accepted root at its tag6 application is the
original bottom root with that exact supplied raw certificate. -/
def ExactAtomicAuxRootReduction : Prop :=
  ∀ (xs : Entries) (s : Settings) dom cod fn arg cert y, AtomHead fn →
    root xs s (auxRaw dom cod fn arg) cert y = true →
      y = bottomRaw cod ∧ cert = bottomRoot

/-- The only possible original proper context transition out of a
literal tag6 application is the actual function context tag5. The
actual raw right argument is unchanged at this proper-origin tick. -/
def ExactAuxProperFunctionContext : Prop :=
  ∀ tag ws dom cod fn arg y (out : Frame),
    next tag ws (auxRaw dom cod fn arg) y = some out →
    ∃ w targetFn,
      tag = 5 ∧ ws = [w] ∧ y = auxRaw dom cod targetFn arg ∧ out = (fn,w,targetFn)

/-- Keep actual input witness bytes via their original parser. Either
the literal root wrapper or the actual one-function-context wrapper
and its supplied child root wrapper appear. No replacement witness. -/
def AuxStepShape (dom cod fn arg witness y : Nat) : Prop :=
  (unpackNode witness = some (0,[bottomRoot]) ∧ y = bottomRaw cod) ∨
  (∃ stored name child,
    fn = freeRaw stored name ∧
    unpackNode witness = some (5,[child]) ∧
    unpackNode child = some (0,[bottomRoot]) ∧
    y = auxRaw dom cod (bottomRaw stored) arg)

def ExactAtomicAuxConcreteStep : Prop :=
  ∀ (xs : Entries) (s : Settings) (Γ : List Nat) requested dom cod fn arg witness y,
    AtomHead fn →
    step xs s Γ requested (auxRaw dom cod fn arg) witness y = true →
      admitted s Γ requested y = true ∧ AuxStepShape dom cod fn arg witness y

/-- The actual supplied hop and its two original least checks.
ArgumentMoves from the actual raw predecessor's right argument
points to the visible input argument and, for a function-context
step, to the visible output argument. It does not assume that
the visible input can itself reach the output in arbitrary Settings. -/
def AuxAcceptedHop (xs : Entries) (s : Settings) (Γ : List Nat)
    (requested dom cod fn arg code y : Nat) : Prop :=
  ∃ q w r argRaw,
    hopView code = some (y,q,w,r) ∧
    q = auxRaw dom cod fn argRaw ∧
    step xs s Γ requested q w r = true ∧ admitted s Γ requested r = true ∧
    least s Γ requested q = some (auxRaw dom cod fn arg) ∧
    least s Γ requested r = some y ∧
    ArgumentMoves s.equivalentHeads argRaw arg ∧
    ((unpackNode w = some (0,[bottomRoot]) ∧ r = bottomRaw cod ∧ y = bottomRaw cod) ∨
    (∃ stored name child outArg,
      fn = freeRaw stored name ∧
      unpackNode w = some (5,[child]) ∧
      unpackNode child = some (0,[bottomRoot]) ∧
      r = auxRaw dom cod (bottomRaw stored) argRaw ∧
      y = auxRaw dom cod (bottomRaw stored) outArg ∧
      ArgumentMoves s.equivalentHeads argRaw outArg))

def ExactAtomicAuxAdvance : Prop :=
  ∀ (xs : Entries) (s : Settings) (Γ : List Nat) requested dom cod fn arg code y,
    AtomHead fn →
    advance (step xs s Γ requested) (least s Γ requested)
      (some (auxRaw dom cod fn arg)) code = some y →
    AuxAcceptedHop xs s Γ requested dom cod fn arg code y

/-- The actual original positive witness is nonempty and its own
decoded hop list has length one or two. Two hops require a literal
free function, its actual bottom-function image, then bottom at the
whole original result type. No third hop can start from bottom. -/
def ExactAtomicAuxPositivePath : Prop :=
  ∀ (xs : Entries) (s : Settings) (Γ : List Nat) requested dom cod fn arg witness y,
    AtomHead fn →
    NumberedWindowPositivePathAlgorithm.positive (step xs s) (least s) Γ requested
      (auxRaw dom cod fn arg) witness y = true →
    (∃ e, unpack witness = some [e] ∧
      advance (step xs s Γ requested) (least s Γ requested)
        (some (auxRaw dom cod fn arg)) e = some y ∧
      AuxAcceptedHop xs s Γ requested dom cod fn arg e y) ∨
    (∃ e₀ e₁ stored name midArg,
      fn = freeRaw stored name ∧ unpack witness = some [e₀,e₁] ∧
      advance (step xs s Γ requested) (least s Γ requested)
        (some (auxRaw dom cod fn arg)) e₀ = some (auxRaw dom cod (bottomRaw stored) midArg) ∧
      AuxAcceptedHop xs s Γ requested dom cod fn arg e₀ (auxRaw dom cod (bottomRaw stored) midArg) ∧
      advance (step xs s Γ requested) (least s Γ requested)
        (some (auxRaw dom cod (bottomRaw stored) midArg)) e₁ = some y ∧
      AuxAcceptedHop xs s Γ requested dom cod (bottomRaw stored) midArg e₁ y ∧
      y = bottomRaw cod)

end LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionTargets
