# Generic bounded descent in the original internal calculus

This is a six-target prerequisite for the paper 06 `lem:id1` continuation.
It freezes an explicit guarded numeric normalization algorithm and internal
graph properties of that algorithm. It does not identify the algorithm with
the original least-code representative, replace the original canonical typed
carrier, or promote a numbered paper statement.

## Original syntax and the two arbitrary leaves

`representative` and `valid` range over **all** unary
`GorbowPRProgram.Program` ASTs. They are called `R` and `V` below. No
calibration, Boolean-output, canonicality, termination, preservation,
idempotence or fixed-point hypothesis restricts these leaves.

Every new program is built using only the unchanged original `Program`
constructors and existing explicit program definitions. In particular:

- `sameLeft` has inputs `[candidate, original]`. It applies the literal
  original `InternalUnpair.left` to each and compares the outputs with
  `InternalEqualityTest.equalityTest`.
- `candidateValid V` applies the actual leaf `V` to coordinate zero.
- `guard V` conjoins `InternalLessThan.ltTest`, candidate validity and
  `sameLeft`, using the existing **exact-one** conjunction. `ltTest` receives
  `[candidate, original]`, so it tests `candidate < original`, not the reverse.
- `choose V` has inputs `[candidate, original]`. The original conditional
  receives control, zero branch, nonzero branch. Those branches are
  respectively coordinate one and coordinate zero.
- `transition R V`, abbreviated `T`, is the composition of `choose V` with
  `[R, projection 0]`. Thus its numerical reading is

      r := R(x)
      T(x) := if r < x and V(r) = 1 and left(r) = left(x) then r else x

  The candidate is computed by the outer composition before the continuation
  uses it. There is one `R` leaf occurrence in this outer argument vector.
  Neither `R(x) != x` nor nonzero validity is substituted for the stated tests.
- `normalizer R V`, abbreviated `B`, is exactly the composition of
  `InternalNumericIteration.repeatProgram T` with `[Program.succ, projection 0]`.
  Its numerical reading is `T` iterated **x+1 times**, starting at **x**.

The existing repeat program is ordinary numeric primitive recursion on inputs
`[count, initial]`; its step inputs are `[predecessor, recursive result,
initial]` and it feeds only coordinate one to `T`. This is not a raw-list
recursor, source-payload recursion, externally supplied fuel, or a choice of
a primitive-recursive representation witness. No original AST is changed.

## Literal graph formulas and quantifiers

`unaryGraph p out input` is the unchanged `InternalControlGraph.programGraph`
at the singleton input vector. That graph is the original
`OrdinaryArithmetic.graphFormula p` embedded into the original language.
The graph is not a standard-model evaluation predicate or a new atom.

`validGraph V x` is the graph of **V** at output `succTerm zeroTerm` and input
`x`. `leftGraph typ x` is the graph of **InternalUnpair.left** at output
`typ` and input `x`. `atMost a b` abbreviates the embedded original strict
arithmetic formula `a < succTerm b`.

Each target quantifies an arbitrary `body : Positive (Fin 1)`, actual unary
leaves `R,V`, variable type `alpha`, **arbitrary derivation context**
`Gamma : List (Formula alpha)`, and the indicated symbolic original
arithmetic terms. The conclusion is always
`Nonempty (InternalCalculus.Derivation body Gamma ...)`. The contexts and
terms are not restricted to the empty context, closed numerals, valid source
terms, or well-formed encodings. All displayed hypotheses below are inside
the original object-language formulas.

## Six frozen targets

With `G_T(out,x)`, `G_B(out,x)` and `Repeat_T(out,k,x)` denoting the above
literal original graphs:

0. **Zero transition:** derive `G_T(0,0)` without premises.
1. **Fuel fixed point:**
   `(value <= fuel AND Repeat_T(out,fuel,value)) -> G_T(out,out)`.
2. **Normalizer bound:** `G_B(out,x) -> out <= x`.
3. **Normalizer fixed point:** `G_B(out,x) -> G_T(out,out)`.
4. **Normalizer validity:**
   `G_B(out,x) -> (G_V(1,x) -> G_V(1,out))`.
5. **Normalizer left tag:**
   `G_B(out,x) -> (G_left(typ,x) -> G_left(typ,out))`.

The fixed-point conclusion is specifically **T(out)=out**, not B(out)=out,
R(out)=out, or an opaque canonicality assertion. Validity of the input is
required only in the validity-preservation implication. A supplied symbolic
tag is required only in the tag-preservation implication. The bound and
fixed-point conclusions are unconditional consequences of the normalizer
graph, including malformed inputs.

## Mandatory zero-case and induction review

The stronger target intentionally allows `fuel=0`; it is not silently changed
to a positive-fuel statement. Zero iterations alone only identify `out` with
`value`. Review must also retain the consequence of `value <= 0` and the
unconditional transition target at zero. For arbitrary `R(0)` and `V`, no
candidate can pass the strict `candidate < 0` guard. Replacing that guard by
a non-increase test would remove this argument and is forbidden.

The existing original numeric-iteration zero, front-successor and fixed-point
interfaces are available as internal suppliers. The intended stronger bound
has the necessary successor arithmetic: after a genuinely descending first
transition from `value <= succ fuel`, the next value is at most `fuel`.
The rejected branch is already a transition fixed point. These are review
obligations for the future original-calculus proof, not additional assumptions
or a proof supplied by this freeze. Full-language internal induction,
arithmetic, graph totality/functionality and exact control/selector equations
must discharge the obligations. Standard-model reflection is not permitted.

## External source identification is a separate later task

Paper 06, lines 551-556, specifies least-code representatives of the original
primary-equivalence classes. The future use of this prerequisite must preserve
that original numerical function and its malformed-input behavior.

Relevant existing source results, pinned for correspondence but **not imported
or assumed by these generic targets**, are:

- `NumberedLeastCodeRepresentativeProof.representativeMinimal`, with original
  primary reflexivity, gives the original representative bound on valid inputs.
  The already checked `NumberedRepresentativePrimrecProof.representativeBound`
  also states the bound directly for arbitrary packed terms and windows.
- `NumberedNumericApplicationSupportProof.decodedRepresentative` gives a
  same-type universe representative and unchanged representative code on that
  representative, under its literal subtype-closure and universe hypotheses.
- `InternalQuotientEdgeChecker.sourceRepresentativeValue` retains the original
  universe decode and its zero default; its target counterpart uses the
  packed decoder instead. They are not interchangeable.

A possible later wrapper is `D(x) = if V(x)=1 then B(x) else R(x)`, using
exact-one normalization. On original source-valid inputs, identification of
`B` with `R` needs the original bound, valid same-type representative and
idempotence results. The false branch preserves the original `R` output on
all remaining inputs. **This packet neither defines that optional wrapper nor
states or proves its all-input calibration.** It also does not conclude that
T-fixed alone means canonical for arbitrary leaves.

The eventual carrier `valid + original tag + T-fixed` and its equality to
the original canonical carrier need separate source-specific calibration and
internal consumer work. No old typed checker, step checker, representative
wrapper, source decoder, target decoder or frozen target is replaced here.
The current representative-fold/certified-result/application obligations,
`CertifiedApplicationLift`, and the closed all-term endpoint remain pending.

## Freeze and validation boundary

Only these three new Lean specification files and this new evidence directory
are written. `FROZEN-SPECIFICATION.json` pins the specification and this
correspondence. `SOURCE-PINS.json` pins selected original syntax, calculus,
internal APIs, external correspondence sources and the original paper; it is
not a successful compiled dependency-closure receipt.

Independent specification review and native preflight are pending. There is
no proof file, theorem implementation, compiler call, native axiom audit or
acceptance claim in this freeze. Proof authorship must wait for independent
review and the coordinator's release. Any later native check must use only
`scripts/check.py` under a fresh sole compiler-slot grant, preserving the
2048 MiB heap / 1536 MiB process-tree RSS / 2048 MiB minimum-free / one-thread /
90 CPU-second / 180 wall-second profile and existing upstream cache.

No added axiom, `sorry`, `admit`, native decision shortcut, unsafe proof,
semantic reflection, target weakening, global register edit, full-root build,
remote CI or Git action is authorized by this packet. The only admissible
axiom closure remains `propext`, `Classical.choice` and `Quot.sound`.
