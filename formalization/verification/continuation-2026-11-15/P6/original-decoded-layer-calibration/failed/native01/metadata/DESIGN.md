# Concrete original decoded layer calibration (exact3)

## Actual gap and duplicate check
ConcreteHeadMoveLayer has constructor internal laws with V explicit, but no
unconditional all-input native layer theorem. HeadMoveFields.NativeFields and
ResultStructuralFields.NativeFields require a fully calibrated U, although the
concrete AST overwrites all live non-answer slots. Supplying false calibration
for its zero fillers would be invalid. TransparentExchangeLayer.NativeOptional
correctly requires calibration only at non-answer slots14/15, and can assemble
the existing concrete AST with actual live field theorems.

## Exact source/AST
TransparentExchangeLayer.validValue decodes original Node at input0 and original
Window at input2, ignores input1. guard is the conjunction of paid Node accepted
(composed on inputs0,2) and paid window (input2). No codec changes.
layer is literally ConcreteHeadMoveLayer.layer n arity guard. Its fallback is
Some0 encoded1, never missing0. The accepted body's existing answer slots use
exact-one conversion and missing-slot defaults; malformed answer lists retain
original decoder getD[] semantics. NativeLayer quantifies every vector, not
just canonical source-code/window/list images.

## Constructive proof plan
Native guard: original node product decoder calibration and paid all-raw window
calibration, then conjunction case split. Native layer: calibrate slots0..13
from actual tags/encoded metadata/children; slot16 from headMove; slots17/18
from head results. Exclude slots14/15 exactly as nativeOptional permits, since
actual answer lookup AST installs them. Do not invoke hU with zero fillers.
Internal guard: recover actual nodeAccepted/windowAccepted composition witnesses,
use observed original pairing inverse on node and parameter, and actual
conjunction introduction/elimination plus checked internal symbols iff bounded
members. All operations stay in internal Derivation; native decoder calibration
is not used to infer graph laws. Left association of the three acceptance
factors is frozen explicitly.

## Remaining limits
No full selected tuple/source E installation or internal recursive exchange
answer equation is claimed. This pays concrete native G and V calibration and
an internal guard criterion; original window closure/type acceptance requirements
for later source arguments remain separate. Prior Window exact3 native gate
passed; independent acceptance pending at freeze. No proofs authored here yet.
