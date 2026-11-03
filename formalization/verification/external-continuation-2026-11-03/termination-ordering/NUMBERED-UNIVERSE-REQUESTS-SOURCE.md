# Actual one-layer finite-universe requests

Paper06 lines551–556 requires effective syntax for the fixed finite type universe. This component connects the existing `NumberedNumericCarrier.universeTest` and `argumentsUniverseTest` to the already accepted typed requests and their literal one-layer expander. It introduces no replacement syntax or decoder.

The local `guard` checks the request's result type in `S` for every term, the domain type in `S` for abstractions, and the original `HeadInWindow arity symbols S (decodeHead head)` for ordinary and numbered heads. The numbered-head check retains the head's original result and base-argument signature even when the auxiliary term has a different result annotation. Argument requests have guard `true`; their emitted term and tail requests perform the original argument checks. `HeadInWindow` retains ranked-symbol membership and every native signature-type membership condition.

`valid` is exactly successful original typed decoding followed by the original term or argument universe test, expressed with `Option.any`. `expandedValid` conjoins the local guard with successful original request expansion and validation of every ordered child. The two frozen target propositions assert equality for every finite symbol type, arity function, symbol list, type list, context, result or argument types, and code, including malformed code. Neither subtype closure nor a prevalidated request is assumed.

This component states one-layer correspondence only. Global guarded evaluation, a sufficient numeric fuel bound, primitive recursion of the universe tests and numeric carrier decoder, primary-class or canonical-representative operations, the complete reduction checker, arithmetic representability, and the whole source theorem remain separate targets.

## Files

- [Definitions](../../../LogicLineages/OrdinalComparison/TerminationOrdering/NumberedUniverseRequestsDefinitions.lean)
- [Exact targets](../../../LogicLineages/OrdinalComparison/TerminationOrdering/NumberedUniverseRequestsTargets.lean)

## Accepted verification

The fixed statement gate and the sixteen-target focused aggregate passed
with actual transitive axiom audits. Frozen semantics and comparison hashes
are unchanged. See [the prospective freeze](UNIVERSE-PRIMREC-FREEZE.json) and
[the acceptance record](UNIVERSE-PRIMREC-ACCEPTED.json) for exact source hashes,
compiler evidence, permitted axioms and verification scope.
