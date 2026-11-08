# Parameterized certified original result-fold closure: frozen prerequisite

This packet freezes three internal derivability targets: the certified-fold
run bridge, generic leaf closure and original application closure. It contains
only definitions, targets, preflight comparators and the source freeze. The
proofs, native preflight and exact axiom audits remain separate gates. No
numbered source statement is promoted.

## Original source and purpose

Paper 06, `06-godel-t-termination-ordering/paper.tex`, lines 537-549, gives
the original well-typed numbered reduction rules. Lines 551-556 retain the
primary-equivalence quotient, least-code representatives and arithmetic H/R;
lines 558-560 state `lem:id1`, the arithmetic accessibility lemma. This
component is an internal machine-closure prerequisite, not a replacement of
those source relations or a completion of the lemma.

The accepted original certified-fold bridge, application closure and leaf
closure supply the proof architecture. The accepted parameterized local
stack laws and the separately frozen parameterized stack-composition
interface supply actual graph laws with an unchanged symbolic parameter.
No external semantic calibration is used as an internal proof rule.

## Literal certified formula and parameter order

The only certified formula is the conjunction of two actual graph formulas:

- `goodRunP G L C (value,p) = 1`;
- `foldP G L C (value,p) = out`.

`goodRunP` is reused from the frozen parameterized fold-calibration definition:
the unchanged original `goodState` AST composed with the actual `runP`.
`goodState` requires exact-one status, empty work and exactly one result.
That result may be zero. Empty results, nonempty work, non-one status and
multiple results are rejected. The raw output selector's default zero does
not certify any of those rejected shapes. This packet neither defines a new
success test nor invokes the external assertion that every natural run passes.

Callbacks remain arbitrary `G L : Program 2` and `C : Program 5`, chosen
before the variable type, context and symbolic terms. Their inputs are
`[whole original value,p]` and `[d,e,functionOutput,argumentOutput,p]`.
The same symbolic parameter occurs in each child, parent, transition,
iterator and callback. It is never existentially selected or placed in the
original state, visit/finish frame, result entry or source encoding.

## Three exact context-uniform targets

0. **Certified-fold/run bridge.** Actual right-selector, visit-work and
   singleton-result constructor graphs fix `payload`, `[visit value]` and
   `[out]`. Under these graphs, `certifiedFoldP out value p` is internally
   equivalent to `actualRunP (payloadFuel payload) work 0 singleton p`.
   `payloadFuel payload` is the existing literal `succ(payload+payload)`.
   `actualRunP` retains both original encoded-state witnesses: initial
   `liveState [work,0]` and terminal `emptyState [singleton]`, joined by the
   actual parameterized iterator graph. It is not replaced by a Boolean or
   semantic completion predicate.
1. **Generic leaf closure.** The exact graph `openGuardP G (value,p)=0`
   conjoined with `L(value,p)=out` internally implies the certified parent
   formula. The existing opening guard includes the original tag-two test
   and exact-one G. Payload, work, singleton results and state witnesses
   must be introduced internally. The target assumes no successful run,
   source validity, output bound or nonzero output. Malformed original inputs
   and zero outputs remain included whenever those actual branch graphs hold.
2. **Original application closure.** The unchanged `applicationConstructors`
   contains actual arrow-list, function-pair, argument-pair and packed-parent
   graphs with shared `d`, `e`, `fp` and `ap`. Together with `G(parent,p)=1`,
   certified children at that same p and `C(d,e,fo,ao,p)=out`, these imply
   `certifiedFoldP out parent p`. C receives function before argument even
   though the original result stack places argument before function. The
   parent run remains the actual `runP` at its own original payload fuel.
   No freely chosen or enlarged budget is substituted for that conclusion.

All three propositions quantify over arbitrary positive body, context Gamma,
variable type and symbolic terms. The original bridge and application public
targets used the empty context, but their accepted proof helpers are already
context uniform. Exposing that existing uniformity here requires no new
semantic assumption and permits direct later graph consumers.

## Intended internal proof route

Reuse the accepted original bridge's fuel, initial-state, good-state and
singleton-result lemmas. Adapt only the actual program composition/recovery
to binary runP and ternary iterateP at p. Preserve actual witness extraction
and introduction in both bridge directions.

For the leaf branch, use the checked actual parameterized local leaf graph,
then the actual parameterized terminal fixed-point iteration for the unused
original fuel. This does not enlarge fuel. Internally produce the original
payload/work/singleton/state witnesses and finish through the bridge.

For application closure, reuse the original constructor queries and fuel
arithmetic from the accepted application proof. Compose the actual child
runs using the frozen parameterized work-append and result-suffix-frame
interfaces, at one identical p and through the whole intermediate result
stack. Use the actual parameterized opening and finish graph rules. Original
empty-work terminal steps consume only the remaining ORIGINAL parent budget.
No claim of an untouched work suffix after a padded first run is required.

The parameterized composition packet is independently undergoing acceptance;
its exact definitions/targets/preflight are pinned, but its mutable proof and
acceptance files are not pinned or assumed accepted here. The parameterized
external fold-calibration packet contributes only its frozen definition of
`goodRunP` and its frozen specification files. No external calibration proof,
semanticFoldP equation or truth-to-derivability reflection supplies any target.

## Freeze and gates

`FROZEN-SOURCE-PINS.json` pins the three new Lean files and this correspondence.
`SOURCE-PINS.json` pins their local import closure, selected accepted original
and parameterized local suppliers, and only the definitions/targets/preflight
of the pending composition and calibration packets. It also pins the original
manuscript and stable build configuration. The pending packets' mutable proof,
receipt, acceptance and summary files are deliberately excluded.

`STATIC-CHECKS.json` records exact target/alias coverage, delimiter and source
shape checks, import closure, original-AST/fuel reuse and hash verification.
Static checking is not Lean elaboration. No new proof body, compiler run,
compiler slot or Git action is part of this freeze.

Later native work requires independent frozen-byte review and explicit sole-
slot admission via `scripts/check.py`. Keep the existing 2048 MiB heap cap,
1536 MiB process-tree RSS cap, 2048 MiB minimum-free guard, one thread,
90 CPU seconds and 180 wall seconds per checker process, using the pinned
upstream cache. The hard cutoff is 2026-11-08 18:00 UTC. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted theorem axioms.

## Exclusions

No external calibration target is duplicated. No unconditional internal
success assertion, canonical leaf selection, representative identification
or congruence, uniform canonical/path correctness, unconditional
`CertifiedApplicationLift`, source constructor/lambda/substitution closure,
all-term accessibility or paper06 `lem:id1` completion is claimed. No new
interpreter, parameter-specialized unary AST, source/state encoding, fuel
policy, accepted source, global target register, dependency or CI change is
made. No full-root build, remote CI or publication is claimed.
