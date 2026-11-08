# Canonical descent selection: frozen prerequisite

This packet freezes ten supporting targets toward paper 06 `lem:id1`.
It does not prove them, promote any numbered source statement, or replace an
accepted source file. Independent static review must precede native preflight
and proof authorship. No compiler has been run for this packet.

## Original source and unchanged mathematical carrier

Paper 06, `06-godel-t-termination-ordering/paper.tex`, lines 537-559, fixes a
finite subtype-closed set of types, the original numbered auxiliary terms,
primary equivalence, least-code representatives, and the induced quotient
one-step/positive-path relations. In particular, lines 551-556 require the
least-code representatives rather than arbitrary valid source terms.

The exact existing numerical carrier is
`NumberedTypedCarrier.typedCanonicalCarrierTest`. At inputs `[value,type]`,
`InternalOriginalTypedCarrier.typedValue` first applies the ORIGINAL
`NumberedNumericDecoding.decodeType` to the requested type coordinate. It
then applies the original source-universe decoder to value, requiring both
the decoded root type and the original least representative code to agree.
The frozen new typed-calibration target is equality to this unchanged
function on **every** natural input vector. It is not restricted to canonical
inputs, valid values, successful decodes, encoded types supplied beforehand,
or accepted original checker inputs.

All source-type, symbol, window, context and precedence parameters retain
their original order and domain. The external calibration targets explicitly
require subtype closure. No claim about preservation by the new selection
on non-subtype-closed windows is made. This is not a restriction of the
all-natural-input domain for any fixed admissible window.

## Separate minimal leaf interface

The existing `InternalCertifiedSourceGuardSelection.Data` carries an old typed
checker and exposes successful fold-run and fold-fixed conjuncts. This packet
does not edit that interface or assert those obligations are now discharged.
Instead it defines `InternalCanonicalDescentSelection.Data` with exactly:

- `oldValidity : InternalOriginalStepGuard.Data`;
- `member : Program 1`;
- `oldEdge : InternalQuotientEdgeChecker.Data`.

Each field contains only finite original Program ASTs. There is no proof,
calibration, output-preservation, fixed-point, termination, reflection,
congruence or certified-lift field. The old edge interface includes its three
original ASTs, but the new transition uses **only oldEdge.targetRepresentative**
as its representative leaf. It does not use oldEdge.sourceRepresentative in
place of the packed-target representative.

`Calibrated` asks for the existing external all-input calibrations of these
leaves. `SelectedCalibrated` asks for existing external interfaces of the
constructed recursive validity, selected edge data and selected typed checker.
Neither is an object-language inference rule, and neither is a Data field.

## Literal selected Programs and fallback behavior

Let `R = data.oldEdge.targetRepresentative` and
`V = (InternalApplicationValidityStack.recursiveData data.oldValidity data.member).sourceValid`.
These are the SAME ASTs in every use below. Recursive validity is already
externally calibrated by the checked
`InternalApplicationValidityCalibrationProof.actualOriginalRecursiveValidityCalibration`.
Its source is the original raw universe test; its target is the packed decoder
without the source window restriction.

The unchanged checked bounded-descent programs are:

    T(x) = if R(x) < x and V(R(x)) = 1 and left(R(x)) = left(x)
           then R(x) else x
    B(x) = repeatProgram T [x+1,x]

Here `left` is literally `InternalUnpair.left`, and B is the original numeric
primitive-recursion AST iterated **x+1** times, starting at x. Neither T nor B
is reimplemented in this packet.

The new generic `fallbackRepresentative R V`, abbreviated D, is the literal
`InternalAcceptance.branch` on `InternalApplicationValidityStack.exactOne V`.
The zero branch is R and the nonzero branch is the existing B:

    D(x) = if V(x) = 1 then B(x) else R(x)

The exact-one normalization is essential. An arbitrary V output of 2 also
selects R. The original branch ordering is control, zero branch, nonzero
branch. There is no new recursion, semantic selector, choice function,
representability witness or fuel parameter.

`edgeData` retains `oldEdge.stepProgram` literally. Its source representative
is D when V accepts and zero otherwise. Its target representative is D on
**all** inputs. Consequently the external all-input target includes these
cases distinctly:

- A malformed packed input retains the original target representative's zero.
- A decoded packed term outside the source universe retains the original
  target representative, which is **not** forced to zero.
- A source-universe input uses B, which must be externally identified with
  the original R by original representative theorems.
- The source representative still returns zero on every source-decode failure.

There is no new target-universe filter, step strengthening, endpoint wrapper,
path wrapper, fold definition or overwrite of existing representative ASTs.

## Exact replacement typed checker

Input coordinates are `[value,type]` throughout. `typedCore R V` is the
exact-one conjunction, in order, of:

1. Actual V applied to coordinate zero.
2. `InternalOriginalTypedCarrier.sameOuterType`, the ORIGINAL left-selector
   equality with coordinate one.
3. The actual equality-test AST comparing T(value) with value.

`typedChecker R V member` additionally puts `member(type)=1` outside that core.
This fourth conjunct is retained to expose original type membership to endpoint
consumers. External calibration must prove it redundant on the original
canonical carrier, not assume it. The old typed checker, any H successful-run
checker, N-fixed condition, R-fixed condition and B-fixed condition are absent
from the selected AST. In particular, T-fixed is not silently interpreted as
canonicality for arbitrary leaves.

The mathematical source identification is separately frozen as target 0.
For source-valid x at a subtype-closed window:

- Original numeric decoding identifies x with the packed code of an original
  source-universe term q.
- `NumberedLeastCodeRepresentativeProof.representativeMinimal`, applied with
  original primary reflexivity, gives R(x) <= x. The checked direct
  `NumberedRepresentativePrimrecProof.representativeBound` is also available.
- `NumberedNumericApplicationSupportProof.decodedRepresentative` gives an
  original source-universe representative r of the **same type**, and proves
  the representative code of r equals R(x). Original packed-code soundness
  then gives V(R(x))=1, matching original left tags, and R(R(x))=R(x).
- If R(x)<x, all three actual transition guards accept and T(x)=R(x).
  If equality holds, the strict guard rejects and T(x)=x=R(x). These exhaust
  the cases because of the original weak bound. Thus, on source-valid x,
  T(x)=x iff R(x)=x. This is an **external** fact, not a new internal rule.
- Apply the same fact at the valid representative to get T(R(x))=R(x).
  Since x+1 is positive, B first reaches R(x) and all remaining iterations
  stay there. This identifies B with R only on the valid branch. D uses R
  on the other branch by construction, so D agrees with original R everywhere.

For the typed carrier, original type-code soundness and total decoding link
raw-left equality to the decoded root type. V plus R-fixed is exactly the
unchanged canonical condition. Root-type membership in S follows from the
unchanged universe definition, so the added membership conjunct does not
change any zero/one output. The original type decoder is not replaced by an
assumed totality axiom, and a successful typed decode is not a target premise.

This is a mathematical specification check and proof plan, **not** a Lean
proof or accepted theorem. These source facts are pinned as prospective
suppliers, not added as new premises to the frozen targets.

## Actual internal graphs and ten targets

Every new graph is the unchanged original `InternalControlGraph.programGraph`
(or its existing unary/binary wrapper). Thus it uses the original
`OrdinaryArithmetic.graphFormula` embedded into the existing language, not a
standard-model predicate or a new atomic relation. Exact-one output is the
original successor of zero. Every internal target quantifies **arbitrary**
R,V (and member when used), positive body, variable type, derivation context
Delta and symbolic original arithmetic terms. It assumes neither calibration
nor subtype closure.

0. **Canonical transition identification:** on original source-valid numeric
   inputs, evaluate T equals evaluate R, with the explicit T-fixed iff R-fixed
   consequence. Original minimality and representative preservation are
   required proved suppliers, not extra premises.
1. **All-input D calibration:** evaluate selected D equals original packed-
   target representative value on every natural input.
2. **All-input canonical typed calibration:** selected typed checker equals
   original `typedValue` on every natural `[value,type]` vector.
3. **Selected data calibration:** recursive validity, source/target selected
   representatives and old step, plus the selected canonical typed checker,
   satisfy the existing complete all-input interfaces.
4. **Internal typed factorization:** actual typed acceptance iff
   member(type)=1 AND V(value)=1 AND left(value)=type AND T(value)=value,
   where each displayed equality is its literal original Program graph.
   All four factors are conclusions in the forward direction; no output/tag
   witnesses or semantic source information are pre-supplied.
5. **Internal D validity:** G_D(out,input) -> (G_V(1,input) -> G_V(1,out)).
6. **Internal D left tag:** G_D(out,input) -> (G_V(1,input) ->
   (G_left(type,input) -> G_left(type,out))).
7. **Internal D transition fixed point:** G_D(out,input) ->
   (G_V(1,input) -> G_T(out,out)).
8. **Internal typed D output:** from the exact four graphs G_D(out,input),
   G_V(1,input), G_left(type,input), G_member(1,type), derive actual selected
   typed acceptance of `[out,type]`. Output validity/tag/T-fixed are NOT in
   the antecedent. Input membership is needed because an arbitrary V has no
   internal semantic relationship to member.
9. **Shared selection:** for each original fixed signature/window/context,
   with subtype closure, there exists ONE Data selection satisfying original
   and selected external calibrations and `InternalLaws`. That selected Data
   precedes every positive body, variable type, derivation context and symbolic
   type/value/input/output. `InternalLaws` is a conclusion, not a Data field or
   an assumed supplier; it contains typed factorization and typed D output.

The D validity, tag and T-fixed proofs must select the actual B branch using
the exact-one V input graph, then consume the already checked internal B
validity, left and T-fixed theorems. Unlike B, arbitrary D cannot have
unconditional tag or T-fixed claims on invalid inputs because its fallback R
is arbitrary. The input validity antecedent is therefore explicit in all
three D targets. There is no internal use of external representative
minimality, idempotence, source decoding or natural-number truth.

## Freeze and validation boundary

The only new Lean files are definitions, target propositions and ten preflight
aliases. No theorem implementation, proof file, added axiom, `sorry`, `admit`,
unsafe/native decision shortcut, native elaboration or compiler call is
included. Preflight aliases only name propositions; they do not prove them.
No existing source, frozen target, register, dependency or CI file is edited.
No Git action is performed.

`FROZEN-SOURCE-PINS.json` pins these three new specification files plus this
correspondence. `SOURCE-PINS.json` records full SHA256s for every local module
in the transitive imports of the specifications and prospective checked
suppliers, including public meta imports, together with the source paper,
accepted supplier evidence and toolchain manifests. It is a static source
inventory, **not** a compiled-closure receipt. `FROZEN-SPECIFICATION.json`
records the target list, AST and scope boundaries and hashes the pin maps.

Any later native preflight/proof check requires the coordinator's release and
sole compiler-slot grant, and must use `scripts/check.py` with the unchanged
2048 MiB heap / 1536 MiB process-tree RSS / 2048 MiB minimum free / one thread /
90 CPU-second / 180 wall-second limits and existing upstream cache only.
Allowed final axiom closure remains propext, Classical.choice and Quot.sound.

This prerequisite does not claim a context-uniform Program compiler, general
source fold closure, application representative congruence, quotient-edge or
path lifting, `CertifiedApplicationLift`, constructor/lambda/substitution
closure, the all-term endpoint, `lem:id1`, a numbered source promotion, a
full-root build, remote CI or publication. The old fold/H/N and certified-lift
obligations remain separate pending work; a smaller useful canonical carrier
interface does not itself discharge those consumers.
