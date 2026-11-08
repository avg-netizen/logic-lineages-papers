# Parameterized original application result stack: local prerequisite

This packet freezes eight supporting propositions for the paper 06
`lem:id1` continuation. It introduces actual parameter-uniform PR ASTs and
specifies their local original-calculus graph equations. It does not prove
them. Seven targets concern internal graph derivations; the other is a
separate all-input numeric evaluation calibration. No numbered statement
is promoted.

## Original data and untouched source meaning

The state remains exactly `InternalApplicationResultStack.State`, with
fields `status`, `work`, and `results`, and its existing `encodeState`.
A live state is the original pair of status one and the pair of the two
original numeric list codes. Visits, finish frames, source packed values,
types, payloads, and list cons/tail/head operations use their existing
constructors. There is no new state type, work-frame format, source codec,
or numeric interpreter.

The parameter is NEVER inserted into a work frame, result entry, or the
original state encoding. The existing parameterized numeric iterator does
carry it in an outer pair with the entire original state; that transport
wrapper is not a redefinition of the result-stack state. The parameter
contributes nothing to `fuel`, `fuelValue`, `frameWeight`, or `workWeight`.
The original initial-state constructor and final-output selector are reused
literally.

Fix actual ASTs `G L : Program 2` and `C : Program 5`. Their input orders are
**[original packed value, parameter]** and
**[domain, codomain, function output, argument output, parameter]**.
These ASTs exist before any symbolic arithmetic parameter, variable type,
or context is supplied. There is no family of unary ASTs specialized at a
parameter numeral. No Boolean-range, validity, calibration, representative,
termination, or callback-preservation premise is supplied.

## Literal wiring and transition AST

- `liftP P` is exactly `composition P [projection 0]`, with binary inputs
  **[value, parameter]**. It ignores input 1.
- `appendParameter xs p` is `Fin.lastCases p xs`: indices `i.castSucc`
  receive `xs i`, and the final index receives `p`. It is finite argument
  wiring, not source evaluation. It also covers zero selectors.
- `wireP P selectors` is exactly `composition P` with all original unary
  selectors lifted through input 0 and projection 1 appended last. It is
  used at arities 2 and 5; its generic interface also allows ordinary
  composition/reindexing proofs to be reused.
- `openGuardP G` is the original exact-one conjunction of the lifted
  original constructor-tag-equals-two test and `G`. Its input is the whole
  original packed value, never its payload, type, child, or rebuilt value.
- `leafReturnedP L` composes the original `returnState` with
  **[L(currentValue,p), rest, results]**. The last two programs are the
  original unary selectors lifted through input 0.
- `combinedP C` wires the four original selectors
  **[left currentValue, right currentValue, head(tail results), head results]**
  to `C` and appends the unchanged `p`. The function output is passed before
  the argument output, despite argument-first storage on the result stack.
- `finishReturnedP C` composes the original `returnState` with
  **[combinedP C, rest, tail(tail results)]**, with both suffix selectors
  lifted through input 0.

`transitionP G L C` has inputs **[original state, parameter]** and preserves
the original branch tree. The branch order is the original control order
**[test, zero branch, nonzero branch]**:

1. Test the lifted original exact-one status. Rejection returns zero.
2. Test the lifted original work code. Empty work returns projection 0,
   preserving the entire original state.
3. Test the lifted original frame-tag-equals-zero test. A visit tests
   `openGuardP G(currentValue,p)` and chooses the leaf return or the lifted
   original `expanded` program.
4. A nonvisit tests the lifted exact-one frame tag. Other tags return zero.
5. A finish tests the lifted result code and then its lifted original tail.
   Empty and singleton result stacks return zero; otherwise it uses the
   parameterized finish return.

Every state/status/work/tag/result selector retains its original program
and is lifted through projection 0. Expansion remains independent of the
parameter, leaf and combine. All failure outputs are zero. The local packet
does not add a separate internal zero/failure target; the exact all-input
calibration still includes those branches.

`iterateP G L C` is the actual existing
`InternalParameterizedNumericIteration.repeatP (transitionP G L C)`, with
inputs **[count, original state, parameter]**. `runP G L C` composes this
ternary AST with **[liftP originalFuel, liftP originalInitial, projection 1]**.
Thus its fuel is exactly **2 * original payload + 1**, regardless of parameter
or computed output sizes. `foldP` applies the unchanged original `output`
selector to that run. Exposing these programs does not establish full-run
shape, full fold correctness, work append, result framing, or representative
identification.

## Exact targets

All seven internal targets conclude actual
`Nonempty (InternalCalculus.Derivation body Gamma formula)` for every original
positive `body`, variable type and arbitrary context `Gamma`, with arbitrary
symbolic arithmetic terms. The ASTs precede those symbolic terms. No
standard-model truth-to-derivability step is permitted.

0. **Separate evaluation.** For every raw numeric state and parameter,
   evaluation of `transitionP G L C [state,p]` equals the ORIGINAL
   `InternalApplicationResultStack.transitionValue` at `state`, with callbacks
   sliced exactly as `G[value,p]`, `L[value,p]`, and `C[d,e,f,a,p]`. This
   includes malformed states and frames, non-one statuses, zero work,
   insufficient results and arbitrary callback outputs. It is not an
   internal derivation and cannot substitute for targets 1-7.
1. **Unary lifting.** `graph2 (liftP P) out value p` iff
   `graph1 P out value`, internally and at arbitrary p.
2. **Appended-parameter wiring.** Given already-derived actual unary selector
   graphs at the original state, the graph of `wireP P selectors [state,p]`
   is internally equivalent to `programGraph P out (appendParameter values p)`.
   The finitely many premises are derivations of selector graphs, not
   semantic evaluations, a new predicate, or any assumed callback theorem.
   This support rule does not weaken any local transition target.
3. **Opening visit.** Under the ACTUAL original `packedApplication` graph,
   original `visitState` graph, and `graph2 G 1 value p`, the actual binary
   transition graph is iff the original `expandedState` graph.
4. **Leaf return.** Under the original `visitState` graph and
   `graph2 (openGuardP G) 0 value p`, the transition graph is iff the existing
   arity-generic `returned L out [value,p] work results` relation.
5. **Finish return.** Under the original `finishState` graph with
   `[domain,codomain,work,argument,function,resultSuffix]`, the transition
   graph is iff the existing
   `returned C out [domain,codomain,function,argument,p] work resultSuffix`.
6. **Empty work.** Under the original `emptyState` graph, the transition
   graph is iff equality of the output and entire original state.
7. **Terminal iteration.** Under that same original `emptyState` graph,
   the actual `iterateP` graph at every symbolic count and the same p is iff
   equality of the output and entire original state. This includes count
   zero and arbitrary nonzero parameters.

The existing `InternalApplicationResultStackReturnSupportProof.returned`
definition is used directly, not replaced. It internally existentially
quantifies a callback result and constrains it by the actual callback graph
and original `returnState` graph. No callback output is furnished by an
external semantic oracle. Its existing `returnedIntro`, `returnedCases`,
and `InternalApplicationResultStackReturnRelationProof.returnedRecover`
are arity-generic and apply to both new callback arities.

## Reusable proof interfaces, not authored proofs

The later proof work should reuse the accepted original interfaces instead
of copying the 19-query opening proof and rebuilding a parallel state codec:

- `InternalApplicationResultStackCompositionStateProof.liveStateCases`,
  `liveStateFields`, `liveStatus`, `emptyAsLive` and `liveOfValue` expose the
  original live state, fields and status under actual constructor graphs.
- `InternalApplicationResultStackCompositionFrameSupportProof.currentFields`
  exposes original frame fields from actual pair/list graphs.
- `InternalApplicationStepPeelComponentsProof.fieldsAtPairs` exposes the
  original packed application selectors.
- `InternalApplicationResultStackCompositionFrameConstructorsProof` supplies
  `visitStateAt`, `returnStateAt`, `finishStateAt` and `expandedStateAt` for
  the unchanged constructors.
- Original graph composition/recovery, equality transport, arity-generic
  branch rules and the lifting/wiring targets connect these unary selectors
  to the binary transition AST.
- The accepted exact parameterized numeric iteration fixed-point interface
  applies to `transitionP G L C`. Together with target 6 and equality
  reflexivity, it supplies target 7 without a new iteration invariant.

These accepted supplier sources and their exact gates are pinned. The
parameterized numeric iteration packet records a successful seven-alias
exact gate; this packet does not alter that supplier or infer source-specific
correctness from it. No new proof files are created at this freeze stage.

## Paper correspondence and excluded claims

Paper 06 lines 537-549 describe the original numbered source reductions.
Lines 551-556 retain the primary-equivalence quotient, least-code
representatives and arithmetic `H`/`R`; lines 558-560 state `lem:id1`.
This result-stack packet is an implementation and internal-graph prerequisite
for that continuation, not a replacement of any source definition and not
completion of the lemma.

In particular this packet does NOT claim parameterized work append or
result-suffix framing, full fold correctness, uniform canonical selection,
representative identification, uniform path correctness, unconditional
`CertifiedApplicationLift`, constructor/lambda/substitution closure, or
all-term accessibility. The exposed `foldP` is an AST, not any of those
results. No symbolic parameter is replaced by a numeral, no parameter is
inserted into a work frame, and no whole-pair measure or stronger fuel is
used. The external evaluation target remains separate from the internal
calculus throughout.

## Freeze and validation boundary

Three new Lean definition/target/preflight files and this packet are the
only changes made here. `FROZEN-SOURCE-PINS.json` pins their source bytes
and this correspondence. `SOURCE-PINS.json` pins the stable full local import
closure of the specification and selected accepted supplier roots, together
with paper/configuration and supplier acceptance inputs. These hashes are
not native build receipts for this new packet.

`STATIC-CHECKS.json` records noncompiler source-shape, delimiter, definition
arity, target/alias coverage, import-closure, forbidden-token and hash checks.
Static success is not Lean elaboration, proof checking or an axiom audit.
Independent review and comparator-only preflight are pending. No compiler
slot was requested or held; the parameterized descent worker has exclusive
native compiler admission. No proof authorship is authorized until review
and a later explicit release.

Any later native run must use `scripts/check.py` under the unchanged
2048 MiB heap / 1536 MiB process-tree RSS / 2048 MiB minimum-free profile,
with one thread, 90 CPU seconds, 180 wall seconds, the pinned upstream cache,
and explicit serialized admission before the 2026-11-08 18:00 UTC cutoff.
Only `propext`, `Classical.choice`, and `Quot.sound` are admissible theorem
axioms. No global register, dependency, CI, resource-policy or Git change,
full-root build, remote CI run, publication, or numbered promotion is made.
