# Parameter-carrying original numeric iteration

This is a seven-target prerequisite for a future parameter-threaded canonical
pipeline supporting paper 06, `lem:id1`. It freezes one uniform construction
from an arbitrary binary primitive-recursive AST. It does not construct a
parameterized descent procedure, fold, or path checker and does not promote
any numbered source statement. The existing fixed-window proofs do not
automatically generalize to a changing symbolic parameter.

## Literal original syntax and order

Fix an arbitrary `GorbowPRProgram.Program 2` AST `P`, whose inputs are
`[value, parameter]`. Both new AST constructors are defined before the
object-language variable type, terms, or parameter are supplied. Thus `P`
is not chosen after seeing a symbolic parameter or its natural value.

The unary `InternalParameterizedNumericIteration.carryP P` is exactly the
composition of the existing pair program with the existing left projection
and the composition of `P` with the existing right and left projections:

    state |-> pair(left state, P(right state, left state))

Here `pair`, `left`, and `right` mean the actual
`InternalPairing.pairing`, `InternalUnpair.left`, and `InternalUnpair.right`
Program ASTs. They use the original `Nat.pair`/`Nat.unpair` convention, not
the different Gorbow square pairing. No interpreter, code evaluator,
semantic-function representation witness, or new primitive is introduced.

The ternary `repeatP P` has input order `[count, value, parameter]` and is
the literal composition

    right (InternalNumericIteration.repeatProgram (carryP P)
      [count, pair(parameter, value)])

In particular the initializer's projections are **2 then 1**, while the
existing iterator receives **count then initial state**. The original
`repeatProgram` base returns its initial-state input. Its recursion step
receives `[predecessor, recursive result, initial state]` and applies the
transition to projection **1**, the recursive result. This order follows
the unchanged `GorbowPRProgram.evaluate` recursion clause. It is ordinary
numeric recursion, not raw-list recursion and not a fuel-adjusted substitute.

The new `carryGraph` and `repeatGraph` only abbreviate the unchanged
`InternalControlGraph.programGraph` of those literal ASTs. Their output and
every input remain original arithmetic terms. No graph is defined through
standard-model evaluation, and there is no semantic-to-internal reflection.

## Seven exact target meanings

For brevity write `Pair(s,p,v)` for the original pairing program graph,
`Left(p,s)` for the original left-unpair program graph, `P(w,v,p)` for the
actual binary program graph, `C(t,s)` for the new carried-step graph, and
`R(w,k,v,p)` for the new ternary repeat graph. These are all literal graphs,
not claims about a separate semantic function.

1. **All-input evaluation.** For every actual `P` and all natural
   `count`, `value`, and `parameter`, evaluation of `repeatP P` at
   `[count,value,parameter]` equals
   `Nat.iterate (fun x => evaluate P [x,parameter]) count value`.
   There is no canonicality, successful-decoding, or positive-count premise.
   This is a separate standard-model calibration target, never an internal
   proof supplier by reflection.
2. **Actual carried step.** Given both `Pair(state,p,value)` and
   `Pair(nextState,p,next)`, `C(nextState,state)` iff `P(next,value,p)`.
   Both state encodings are actual graph hypotheses, not external equalities
   or newly added term constructors. The parameter is identical in both.
3. **Internal parameter preservation.** Given `Left(p,state)` and the
   original `InternalNumericIteration.repeatGraph (carryP P) out count state`,
   derive `Left(p,out)`. This covers every arbitrary raw initial state and
   every symbolic count. It does not require a supplied right-coordinate
   witness or a generated-state assumption.
4. **Zero.** `R(out,0,value,p)` iff `out = value`.
5. **Front successor.** Given `P(next,value,p)`,
   `R(out,succ count,value,p)` iff `R(out,count,next,p)`.
6. **Addition fusion.** Given `R(intermediate,first,value,p)`,
   `R(out,addTerm first second,value,p)` iff
   `R(out,second,intermediate,p)`. First perform `first` iterations and then
   `second` iterations, keeping the very same symbolic parameter throughout.
7. **Fixed point.** Given the actual graph `P(fixed,fixed,p)`,
   `R(out,count,fixed,p)` iff `out = fixed` for every symbolic count.
   This is full-output equality, not merely acceptance at output one.

Each of targets 2-7 quantifies every `body : Positive (Fin 1)`, `P : Program 2`,
variable type `alpha`, arbitrary context `Gamma : List (Formula alpha)`, and
the displayed arbitrary original arithmetic terms. The result is
`Nonempty (InternalCalculus.Derivation body Gamma formula)`. Hypotheses
displayed above occur inside the unchanged object-language implication.
There is no new calculus, axiom, semantic premise, canonical-state
restriction, fixed natural parameter, or finite/numeral-only count range.

## Existing suppliers and intended later proof boundary

The source pins include the complete current local import closure of the
new specifications and selected existing proof suppliers. In particular:

- `InternalNumericIterationProof.frontSuccForward` and
  `frontSuccBackward` are arbitrary-context internal rules on the actual
  numeric iteration graph, with an actual transition-graph premise.
- `InternalNumericIterationFusionProof.fusionValue` and `fusionRecover`
  supply the two directions of original addition fusion.
- `InternalNumericIterationFixedPointProof.fixedValue` supplies iteration
  of an actual internal fixed point at every symbolic count.
- `InternalNumericIterationSupportProof` supplies original recursion
  zero/successor values and recovery. Its syntax and the preceding numeric
  targets remain unchanged.
- `InternalApplicationCertificateConstructorsSupportProof.pairLeft`,
  `pairRight`, and `reconstructPair` use the actual original pair/unpair
  graph inverses. Their arbitrary-context statements are retained.
- Existing composition introduction/recovery, graph totality/functionality,
  equality transport, and full-language natural induction supply the graph
  plumbing and preservation argument within the original calculus.
- `InternalPairingEvaluationProof.exactPairingEvaluation` and
  `InternalUnpairEvaluationProof.exactUnpairEvaluation` support only the
  separate all-input natural evaluation proof.

These are possible suppliers for later proof work, not extra premises in
any frozen target. The carried parameter must be shown internally invariant,
then retained in all intermediate actual pair graphs. Existing unary
iteration laws cannot be used by silently closing `P` over a symbolic term.

The source correspondence is supporting rather than a direct completion of
paper 06 lines 537-556 (original numbered application and arithmetic quotient
relations) or lines 558-560 (`lem:id1`). Parameterized descent, uniform
canonical selection, uniform fold/path correctness, an unconditional
`CertifiedApplicationLift`, the remaining constructor/lambda/substitution
arguments, and all-term accessibility are explicitly outside this packet.

## Freeze and validation state

Only three new Lean specification/preflight files and this packet's
correspondence and pin manifests are written. Existing source files, frozen
targets, proof files, register, resource policy, dependencies, and Git are
not changed. `FROZEN-SOURCE-PINS.json` pins the three new Lean files and this
correspondence; `SOURCE-PINS.json` pins existing supplier sources and the
selected original paper/configuration/evidence inputs.

The static checks recorded in `FROZEN-SPECIFICATION.json` check file shape,
target/alias coverage, import availability, source hashes, and forbidden
proof tokens. They are not a Lean elaboration, proof, or axiom-closure check.
Independent specification review and comparator-only native preflight are
pending. No new proof has been authored and no compiler has run here.

This worker has no compiler slot. Any later preflight requires explicit
sole-slot admission and the unchanged `scripts/check.py` profile: 2048 MiB
heap, 1536 MiB process-tree RSS, 2048 MiB minimum free memory, one thread,
90-second CPU and 180-second wall limits, and existing pinned upstream
cache only. The 2026-11-08 18:00 UTC cutoff remains unchanged. No full-root
build, remote CI, acceptance, or Git publication is claimed.
