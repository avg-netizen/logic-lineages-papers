# Parameterized bounded descent in the original internal calculus

This packet freezes six internal supporting targets for the paper 06
`lem:id1` continuation. It specifies a uniform guarded numeric normalizer
whose two actual binary program leaves receive a symbolic runtime parameter.
It does not prove the targets, identify the normalizer with the original
least-code representative, establish uniform fold/path correctness, or
promote a numbered paper statement.

## Actual binary leaves and literal program construction

Fix arbitrary `GorbowPRProgram.Program 2` ASTs `R` and `V`. Each has input
order **[value, parameter]**. They are actual programs before any variable
type, context, or symbolic arithmetic term is supplied. They are not a
family of unary programs specialized after the parameter has been given.
Neither leaf has a calibration, Boolean-range, validity-preservation,
termination, idempotence, canonicality, or fixed-point premise.

The definitions use only existing original `Program` constructors and
explicit original control, arithmetic, pairing, and iteration programs.
There is no interpreter, representation witness, selected semantic function,
new recursion primitive, or truth-to-derivability reflection.

The continuation programs have input order
**[candidate, original value, parameter]**:

- `candidateLess` composes the existing `InternalLessThan.ltTest` with
  projections **0,1**, testing `candidate < original value`.
- `candidateValid V` composes the actual binary leaf `V` with projections
  **0,2**, testing `V(candidate,parameter)`.
- `sameLeft` applies the actual original `InternalUnpair.left` to projections
  **0 and 1**, then compares those outputs using the existing equality-test
  AST. It compares the original type tags of the candidate and original
  **values**, never the parameter or the left coordinates of carried states.
- `guard V` is the existing exact-one conjunction of these three tests.
  Validity means exactly one, not merely nonzero. The conjunction normalizes
  the raw leaf output, so the conditional guard is an exact Boolean result.
- `choose V` uses the original conditional order
  **[control, zero branch, nonzero branch]**. The branches are projection 1
  (original value) and projection 0 (candidate), respectively.
- `transition R V`, abbreviated `T`, has inputs `[value,parameter]` and
  composes `choose V` with **[R, projection 0, projection 1]**. Its numerical
  reading is:

      candidate := R(value,parameter)
      T(value,parameter) :=
        if candidate < value
          and V(candidate,parameter) = 1
          and left(candidate) = left(value)
        then candidate
        else value

  The outer argument vector contains exactly one occurrence of the
  candidate leaf `R`. It carries the unchanged parameter to the validity
  test and returns a value, not a paired state.
- `normalizer R V`, abbreviated `B`, has inputs `[value,parameter]` and is
  the literal composition of `InternalParameterizedNumericIteration.repeatP T`
  with **[succ(projection 0), projection 0, projection 1]**. Thus

      B(value,parameter) := repeatP T [value+1,value,parameter]

  The fuel is **value+1**, not `pair(parameter,value)+1` or a bound on the
  parameter. The actual original arithmetic successor program is used.

## Parameter-carrying iteration supplier

The frozen iteration specifications define, for any actual binary AST `P`,

    carryP P(state) := pair(left state, P(right state,left state))
    repeatP P[count,value,parameter] :=
      right (InternalNumericIteration.repeatProgram (carryP P)
        [count,pair(parameter,value)])

Here `pair`, `left`, and `right` are exactly `InternalPairing.pairing`,
`InternalUnpair.left`, and `InternalUnpair.right`. The numeric iterator uses
the original recursion on **[count,initial state]**; its step receives
**[predecessor,recursive result,initial state]** and feeds projection 1
to the unary transition. No raw-list recursion or additional fuel is used.

The direct `repeatP` graph contract is chosen for this packet. The measured
value is the **right** coordinate of the carried state. The carried left
coordinate retains the parameter but does not measure descent. Separately,
`sameLeft` preserves the original left selector of that right-coordinate
value. These two uses of the left selector must never be conflated.

The iteration packet's definitions, targets, and preflight are stable and
pinned here. Its proofs are still being authored by the separate iteration
worker. **No mutable parameterized-iteration proof is imported or pinned in
this packet**, and no successful exact proof gate for that supplier is
claimed. Its reviewed comparator preflight passing does not establish its
target propositions. Later descent proof work must wait for the actual
internal zero, front-successor, and fixed-point interfaces to be accepted.

## Literal formulas and the six exact targets

`binaryGraph p out value parameter` abbreviates the unchanged
`InternalControlGraph.programGraph p out [value,parameter]`.
The transition and normalizer graph wrappers use their literal binary ASTs.
`validGraph V value parameter` is the actual graph of `V` at output
`succTerm zeroTerm`. `leftGraph typ value` is the actual original left-selector
graph at output `typ` and input `value`. `atMost a b` is the object-language
formula `InternalLessThan.strictLess a (OrdinaryArithmetic.succTerm b)`.
None is an external standard-model evaluation predicate or a new atom.

Write `G_T(out,value,p)`, `G_B(out,value,p)`, `G_V(1,value,p)`,
`Left(typ,value)` and `Repeat_T(out,fuel,value,p)` for these literal graphs.
The frozen targets are:

0. **Unconditional zero:** `G_T(0,0,p)`.
1. **Strong fuel stabilization:**
   `(value <= fuel AND Repeat_T(out,fuel,value,p)) -> G_T(out,out,p)`.
2. **Normalizer bound:** `G_B(out,value,p) -> out <= value`.
3. **Normalizer fixed point:** `G_B(out,value,p) -> G_T(out,out,p)`.
4. **Normalizer validity:**
   `G_B(out,value,p) -> (G_V(1,value,p) -> G_V(1,out,p))`.
5. **Original value-tag preservation:**
   `G_B(out,value,p) -> (Left(typ,value) -> Left(typ,out))`.

Every target quantifies all `body : Positive (Fin 1)`, both arbitrary binary
AST leaves, every variable type, arbitrary derivation context `Gamma`, and
all displayed symbolic original arithmetic terms. The conclusion is always
`Nonempty (InternalCalculus.Derivation body Gamma formula)`. All displayed
premises occur **inside** the original object-language formula. There is no
restriction to standard naturals, closed numerals, empty contexts, successful
decoding, valid source terms, canonical states, or bounded parameters.

In particular the parameter term in every transition, validity and repeat
graph is identical. The symbolic type tag and symbolic parameter are
independent. The fixed-point conclusion is **T(out,p)=out**, not B-fixed,
R-fixed, parameter preservation alone, or an opaque canonicality predicate.

## Zero fuel and later internal induction obligations

The strong target includes `fuel=0` with **arbitrary, possibly nonzero p**.
Zero iterations return `value`; `value <= 0` internally forces `value=0`.
The unconditional zero target must then supply `T(0,p)=0`: no candidate can
pass `candidate < 0`, irrespective of either leaf or the parameter.
The initial carried state `pair(p,0)` need not be zero. A proof that invokes
only the whole-state unary zero case has therefore not discharged this case.

The accepted unary bounded-descent proof provides a reusable internal
induction **pattern**, not an instance whose hypotheses automatically fit:

- Establish the actual binary transition graph split: output equals input
  or is strictly smaller. Establish exact-one validity and original value-tag
  preservation for one step, with the same symbolic parameter.
- Use the actual parameterized zero, front-successor and fixed-point rules
  to expose the first transition and tail at that identical parameter.
- Internally induct on the fuel with a finite universal row quantifying
  input value, output, original type tag **and parameter**. One possible
  stronger row simultaneously carries bound, validity, original tag, and
  the conditional strong-fuel fixed-point conclusion.
- If a first transition is fixed, use the parameterized fixed-point law.
  If it strictly descends from `value <= succ fuel`, original internal
  arithmetic gives `next <= fuel`, so the smaller-fuel row applies.
- Specialize to the actual normalizer graph at `succ value`, retaining the
  same parameter throughout. The graph-totality/functionality, original
  equality transport, and full-language internal induction rules remain
  unchanged.

Existing `InternalBoundedDescentNormalizerInductionProof.zeroCore`,
`successorFixed`, `successorResult`, `allRows` and `repeatResult`, and the
old step/support modules are pinned as accepted proof-pattern sources.
They do not license treating `R` and `V` as unary programs closed over an
arbitrary symbolic term. Nor may the old normalizer be applied to the entire
pair: that would give the wrong fuel and preserve only the parameter as its
left tag. No such reduction or additional premise occurs in these targets.

This is a plan for later proof authorship, not proof code or an extra
assumption. No quantifier swap, semantic induction substituted for internal
induction, or standard-model truth-to-derivability step is permitted.

## Source correspondence and exclusions

Paper 06 lines 551-556 retain least-code representatives of the original
primary-equivalence classes and the original arithmetic quotient relation.
Lines 558-560 state `lem:id1`. This packet is a generic supporting component
toward that setting, not a direct formalization of either complete claim.

Even after these six targets are proved, identifying `B` with the original
representative at every parameter requires separate source-specific bounds,
same-type validity/idempotence, and malformed-input calibration. A T-fixed
value is not automatically canonical for arbitrary binary leaves. Uniform
canonical selection, representative-fold correctness, uniform path checking,
application compatibility, `CertifiedApplicationLift`, constructor/lambda/
substitution closure, and all-term accessibility remain separate obligations.
The original paper, source semantics, decoders, checkers and frozen targets
are not altered. No external evaluation theorem is introduced here.

## Freeze and validation boundary

Only three new Lean definition/target/preflight files and this evidence
packet are written. `FROZEN-SOURCE-PINS.json` hashes the three new Lean files
and this correspondence. `SOURCE-PINS.json` hashes the stable local import
closure of the new specification and selected accepted supplier roots, plus
the stable iteration specification/preflight and selected paper/configuration/
acceptance inputs. It excludes mutable parameterized-iteration proofs.
These are source pins, not source-matched native build receipts.

`STATIC-CHECKS.json` records noncompiler checks of syntax shape, declared
arities/projection order, target/alias coverage, local import availability,
forbidden executable proof tokens, and byte hashes. Static success is not
Lean elaboration, proof acceptance, or an axiom-closure audit. Independent
specification review and native comparator-only preflight remain pending.
No proof files have been authored and no compiler has been run for this
packet. The iteration worker retains the sole compiler slot.

Any later native run needs explicit sole-slot admission and the unchanged
`scripts/check.py` profile: 2048 MiB heap, 1536 MiB process-tree RSS, 2048 MiB
minimum free memory, one thread, 90 CPU seconds, 180 wall seconds, and the
existing pinned upstream cache. The 2026-11-08 18:00 UTC cutoff remains.
The only admissible theorem axioms are `propext`, `Classical.choice` and
`Quot.sound`. No source-register, resource-policy, dependency, or Git changes,
full-root build, remote CI, numbered-source promotion or publication are
claimed or performed.
