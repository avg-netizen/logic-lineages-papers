# Original application result stack: specification correspondence

This is an eight-target supporting prerequisite for paper 06, `lem:id1`.
It is not the representative application-congruence theorem, the original
application-step theorem, or the complete arithmetic accessibility proof.
The comparator is frozen before proof authorship. Native preflight and
independent specification review are still required.

## Original source and scope

The paper's fixed subtype-closed finite type set and original auxiliary
application rule occur at `06-godel-t-termination-ordering/paper.tex`, lines
537–549. Its least-code representatives and quotient edge occur at lines
551–556. This packet implements one needed numeric recursion mechanism;
it does not change those term codes, relations, windows or representatives.

Every application is still the literal packed value
`pair e (pair 2 (pair d (pair fp ap)))`. Its children are the original typed
packed values `pair (1 + pair d e) fp` and `pair d ap`. Original `Nat.pair`,
its inverses, and successor/pair natural-list codes are reused unchanged.
The only new codes are private machine frames and its three-field state.

## Concrete computation

The inputs are finite ASTs `guard : Program 1`, `leaf : Program 1` and
`combine : Program 4`. There are no correctness, derivability, recursion,
normalization or representability fields.

- State is `pair status (pair workCode resultsCode)`.
- Visit is `pair 0 originalPackedInput`.
- Finish is `pair 1 (pair originalDomain originalCodomain)`.
- A visit opens only when the original constructor tag is two AND the
  guard on the ORIGINAL WHOLE root returns exactly one.
- Opening replaces the visit by visit-function, visit-argument, finish.
  Existing results are preserved literally.
- A rejected opening pushes `leaf originalPackedInput`. This includes
  every nonapplication and every application outside the chosen guard.
- Finish requires two results and pops argument first, then function.
  Its output is `combine domain codomain functionResult argumentResult`.
  No type-tag or representative property of either output is presumed.
- Unknown frame tags, non-one status and insufficient finish results
  fail to numeric zero. Empty live work is a fixed point preserving the
  entire arbitrary result stack.

The complete finite bounded AST is also exposed: original numeric primitive
recursion runs the explicit transition with `2 * originalPayload + 1` fuel.
Its output selector accepts only live empty work with exactly one result.
Exposing this AST does NOT prove its recursive application equation, result
stack invariant, all-input representative calibration or successful final
shape. Those are explicitly separate future targets.

## Exact weight and budget

A visit has weight `2 * originalPayload + 1`; every other frame has weight
one. The result stack contributes nothing, because outputs may grow without
bound. The checked original application bound is
`functionPayload + argumentPayload + 2 <= rootPayload`.
Consequently the opened work prefix has weight
`2 * functionPayload + 2 * argumentPayload + 3`, strictly below the visit's
`2 * rootPayload + 1`. Opening plus the two child budgets plus finish also
fits within the root budget:
`1 + (2 * fp + 1) + (2 * ap + 1) + 1 <= 2 * rootPayload + 1`.
Reconstructed arrow types and computed results never enter either bound.

## Eight exact targets

1. All-raw-state evaluation calibration of the actual transition AST.
2. Literal compatibility of the numeric and structured state transitions,
   including malformed frames/status and short result stacks.
3. Strict work-weight decrease for every nonempty live state.
4. Exact exposed fuel calibration, initial weight and application budget.
5. Internal opened-visit equation from actual constructor/state graphs and
   the actual root guard graph at one.
6. Internal fallback equation from the actual opening-test graph at zero,
   with the actual leaf output quantified internally.
7. Internal finish equation from the literal frame/result constructors,
   with the actual combine output quantified internally in correct order.
8. Internal empty-work fixed-point equation preserving the whole result
   stack, not merely a Boolean success result.

The internal formulas use arbitrary symbolic codes and the original
arithmetic `programGraph`. No natural-number truth is reflected into the
calculus. In particular, external calibration cannot discharge their guard
graphs or any later application recursion premise.

## Planned use, not asserted in this packet

For a fixed valid window `S` with its original subtype-closure proof, the
intended common representative normalizer opens only source-universe-valid
original roots. Its leaf is the original target representative; its combine
constructs an original application from the normalized children and applies
that target representative. An explicit codomain/payload tag wrapper may
be used in the later combine AST if needed for internal type transport,
but this packet assumes no output tag property.

The eventual source representative is zero on original source-invalid
inputs and the common normalizer on source-valid inputs. The eventual
target representative is the common normalizer on every input. Bad windows
retain the old programs. The original representative-application congruence
under the valid-window hypothesis must prove the external valid branch;
both original children must first be shown in the universe. Nonuniverse
and nonapplication roots must retain exact old target behavior.

Output-preserving continuation/framing for the actual numeric iterator is
still required. The checked Boolean `successfulWorkAppend` does NOT supply
it: that theorem permits the attached suffix to start early and concludes
only success at summed fuel. It cannot be reused as an equality of states
or outputs at an intermediate count.

No fixed-Gamma or context-uniform representative package is completed here.
Later calibration must preserve fixed-Gamma original functions first; joint
context, outer malformed-object handling, typed-entry exposure and
vertex/full-context dispatch remain separate. Numeric-step soundness may
later justify an externally redundant target-universe guard under the valid
window hypothesis. No strict-precedence assumption is introduced.

No numbered source statement changes status. No compiler, proof author,
global-root build, Git operation, publication or remote CI is claimed.
