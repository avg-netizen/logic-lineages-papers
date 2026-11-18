# Independent typed-spine exact pre-scope review

Approved for proof authoring and later native checking. All frozen pins match.
Inspected actual SpineTyping and all seven SpineTypingTargets against the
approved plan and current original-spine syntax/application definition.

BoundContext.prefix is nearest-binder-first, agreeing with reversed consumed
lambda accumulation. Free names use recorded type/name pairs; bound indices
must match their recorded type in the context. Head bases retain original
declarations, while marked extras are individually typed and output may be
retyped, exactly as auxiliary syntax permits. CallTyped decomposes the original
arrow and types every external argument in the same outside context.

ParallelPreserves/Base/Extras each take an actual finite typed value list and
source typing under its prepended type context. They have no caller-supplied
SubCompatible or output-validity premise. The local SubCompatible definition
is available only to internal structural helpers; endpoint preservation must
discharge it. ShiftCompatible is explicitly restricted to the shift transport
helper, not hidden in the call endpoint.

ConsumeExact asserts the actual consumeTypes result from typed arguments.
CallPreserves has exactly source typing, typed original argument spine and
actual apply success as premises, concluding actual result typing. It does
not replace apply with a typed implementation or weaken original-variable
blocking. AnnotationExact is correctly separate from preservation.

This is a concrete typing theorem for the locally nameless auxiliary carrier,
not a bridge to the earlier named typing presentation or alpha quotient. It
remains separate from successful application covariance, weak/strict comparison
closure and complete manuscript theorems. No native check performed here.
