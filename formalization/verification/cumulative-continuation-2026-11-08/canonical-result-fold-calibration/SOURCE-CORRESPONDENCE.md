# Canonical result-fold calibration: frozen external targets

This packet freezes five supporting external calibration targets for the exact
canonical fold introduced by `InternalCanonicalResultFoldOpening`. It contains
definitions, target propositions and preflight proposition aliases only. No
proof authorship, native preflight, compiler launch, source-register change or
Git action is included. Independent review must precede native preflight and
proof work. The separately owned internal invariant is not a dependency here.

## Original source and unchanged selection

Paper 06, `06-godel-t-termination-ordering/paper.tex`, lines 537-549 fixes the
finite subtype-closed type window and original auxiliary application. Lines
551-556 require the original least-code primary-equivalence representatives;
mere well-typedness is not a replacement. Lines 558-560 state `lem:id1`.
This packet is an external supporting component, not that internal theorem.

Every target quantifies one existing `InternalCanonicalDescentSelection.Data`
and uses its actual original-leaf `Calibrated` proposition at the same n,
arity, symbols, S, Gamma and table. The only additional source assumption is
`SubtypeClosed (fun tau => tau in S)`. No new Data record or correctness field
is introduced. In particular the fixed selection is literally:

- R = `data.oldEdge.targetRepresentative`;
- V = `(InternalCanonicalDescentSelection.validity data).sourceValid`, the
  checked recursive SOURCE validity, not merely packed-target decoding;
- member = `data.member`;
- D = `InternalCanonicalDescentSelection.fallbackRepresentative R V`;
- G = `InternalCanonicalResultFoldOpening.rootGuard V member`;
- C = `InternalCanonicalResultFoldOpening.combine R V`;
- N = `InternalCanonicalResultFoldOpening.foldN R V member`;
- H = `InternalCanonicalResultFoldOpening.goodRunH R V member`.

The new aliases only specialize these exact existing ASTs. All prior definition,
target and proof files remain unchanged. There is no equality-based replacement
of an internal graph and no reliance on the in-progress internal invariant.

## Actual guard, leaf and combine

G tests exact-one V at the WHOLE original root, exact-one V at both ORIGINAL
reconstructed children, and exact-one member at the original root's raw LEFT
codomain. It does not inspect normalized children. The result stack separately
wraps G in its unchanged constructor-tag-two `openGuard`.

Only the complete opening decisions are claimed equal:

    evaluate(openGuard G, x) = evaluate(openGuard V, x).

For a nonapplication raw root both sides are zero. Nothing states G=V on that
branch. For a tag-two raw root, calibrate V and member and use the checked
`InternalApplicationValidityStackInvariantProof.sourceAppAcceptance`:

    sourceValid(x)=1 iff member(codomain(x))=1
      and sourceValid(originalFunctionChild(x))=1
      and sourceValid(originalArgumentChild(x))=1.

This proves the extra guard factors are redundant exactly where the original
application opens. The facts come from the actual original source universe,
not from target decoding, arbitrary typed-child premises or an assumed rule.
Conversely G already includes V(root), so a G-open root is source-valid.

D uses bounded descent on source-valid inputs and the original R fallback on
every other input. The checked all-input canonical descent calibration therefore
gives D(x)=the original packed-target representative of x for every x. No input
validity or canonicality is required, including on decoded nonuniverse inputs.

C takes `[d,e,f,a]`, constructs the exact original raw application

    rawApp(d,e,f,a) = pair(e,pair(2,pair(d,pair(right(f),right(a)))))

and applies D to that whole result. All-input C calibration is consequently
the original target representative at this rawApp, with no premises on d, e,
f or a. There is NO outer `pair(e,right(...))` overwrite. The older
`InternalRepresentativeFoldCalibration.combine` and its codomain-repacking
calibration supplier are preserved but do not prove this new combine result.

## Five exact targets

0. `ActualOriginalCanonicalFoldOpeningCalibration` equates the two full
   `openGuard` outputs on every natural one-vector input. It does not equate
   G and V unconditionally or supply an internal opening rule.

1. `ActualOriginalCanonicalFoldLeafCombineCalibration` states both D's
   all-input original packed-target equality and C's all-input equality at
   `ApplicationCertificateLift.applicationValue v`. The constructor is the
   original raw application on whole child outputs, in the unchanged order.

2. `ActualOriginalSemanticCanonicalFoldCalibration` states that the existing
   independent `semanticFold` at G/D/C is the original packed-target
   representative on every natural input. This semantics is defined by
   well-founded recursion on ORIGINAL payloads, independently of the machine,
   finite fuel or desired representative equality.

3. `ActualOriginalCanonicalFoldProgramCalibration` gives both N(x)=the original
   packed-target representative and H(x)=1 on every raw input. The ACTUAL
   existing finite run, exact singleton shape and `2*originalPayload+1` fuel
   are retained. Generic fold calibration and generic good-run calibration
   must be consumed as already checked suppliers, not new premises. H=1 is
   external natural-number calibration only, never a reflected internal fact.

4. `ActualOriginalCanonicalFoldDataCalibration` calibrates the concrete new
   `edgeData` together with the SAME recursive validity and SAME descent
   canonical typed checker. It preserves the literal old step AST. Target is
   N on all inputs; source is N exactly when V(input)=1 and zero otherwise.
   Source selection MUST use V, not G or either application-only openGuard.
   Thus valid nonapplications retain their original nonzero source behavior.

All five targets are conditional only on subtype closure and the same existing
external Data calibration. No semantic correctness, fold equation, successful
run, recursive closure, representative congruence, input canonicality or
canonicality of recursively computed outputs is added as a target hypothesis.

## Concrete proof route to review, not new assumptions

First specialize the checked recursive validity calibration to the existing
Data, evaluate the original selectors, and use `sourceAppAcceptance` and the
existing `openGuardEvaluation`. Exact-one conjunctions return only zero or
one, so this yields output equality rather than merely acceptance equivalence.
Specialize `actualOriginalCanonicalDescentCalibration` for D and compose it
with the original constructor's checked `applicationEvaluation` for C.

For the semantic target, perform strong induction on the original root payload,
quantifying every original packed input at each bound. In the nonopening branch
use the all-input D equality immediately, without decoding or restricting the
root. In an opening branch, recover original tag two and source validity;
the original decoder and `sourceAppAcceptance` supply both original children
in the source universe. The existing strict child-payload bounds permit the
two induction calls. No packed-code bound, normalized-output bound or output
size estimate enters this argument.

At that open root, use `NumberedNumericApplicationSupportProof.decodedRepresentative`
to obtain genuine same-type, source-universe representatives of both original
children, including equality of their representative codes. The exact original
raw application of those two whole representative codes is the packed code of
their genuine auxiliary application. Apply the NEW C equality, then
`NumberedQuotientApplicationProof.representativeApplicationCongruence` to equate
the original representatives of that application and the original root.
The original source-universe premises and subtype closure are available here;
they are not assumed on every arbitrary raw combine input. The checked
`targetOnPacked` and `applicationSelectors` in the older support module may be
reused because neither states the old combine equation. Do not reuse that
module's `typedApplicationCombine` or `openedRootCombine` as if it described C.

The checked `actualOriginalBoundedResultFoldCalibration` transfers independent
semanticFold calibration to the ACTUAL N AST on all inputs. The checked
`actualOriginalResultFoldGoodRunCalibration` yields H=1 for these same leaves
and fuel. No new termination, execution correctness or good-run hypothesis
is admitted. These two external facts do not license semantic reflection into
the object-language calculus.

Finally use the original source/target relation

    sourceRepresentative(x) =
      if sourceValidity(x)=1 then targetRepresentative(x) else 0.

The already checked `InternalRepresentativeFoldCalibrationProof.sourceFromTarget`
can supply this semantic identity without importing its old combine equation.
The original Data supplies step calibration, recursive validity calibration is
unchanged, and canonical descent supplies the unchanged selected typed-checker
calibration. No tag wrapper is needed: the all-input N equality already retains
the entire original target representative, and the typed AST remains literally
the descent-selected membership/V/raw-left/T-fixed checker.

## Malformed inputs and scope boundaries

Malformed inputs and all decoded nonuniverse inputs are covered, not excluded.
Every root that fails the original source/application opening condition uses D
on the WHOLE original input. D keeps R on source-invalid inputs. The target
representative is not replaced by zero merely because source validity fails.
Only the original source representative selector returns zero in that case.
Target decoding is not strengthened to source-universe decoding.

There is no claim of a computable compiler uniform in S or Gamma. There is no
calibration claim on non-subtype-closed windows and no new choice of the old
leaves per input. The internal canonical fold invariant remains separately
owned, and none of its conclusions is assumed here. Internal representative
application congruence, quotient-edge/path lift, CertifiedApplicationLift,
constructor/lambda/substitution closure, all-term accessibility and paper 06
`lem:id1` remain outside this packet. No numbered source is promoted.

## Freeze, pins and permitted verification

`FROZEN-SOURCE-PINS.json` pins exactly the three new Lean specifications and
this correspondence. `SOURCE-PINS.json` inventories their transitive local
imports and the named prospective checked suppliers, including meta imports,
plus the original paper, checker/toolchain and supplier acceptance evidence.
The inventory is static and is NOT a source-matched native closure receipt.
The separately changing invariant packet is intentionally not inventoried.

Text-only checks verify balanced delimiters, direct import existence, absence
of new theorem/lemma declarations and forbidden proof shortcuts, unchanged
accepted supplier pins and preservation of the exact opening aliases. They do
not elaborate Lean. No proof or compiler was run for this packet.

Any subsequent native preflight or proof work requires independent review and
the coordinator's explicit release and sole serialized compiler-slot grant.
Use only `scripts/check.py` with the unchanged 2048 MiB heap, 1536 MiB
process-tree RSS, 2048 MiB minimum free, one thread, 90 CPU seconds, 180 wall
seconds and the existing upstream cache. Final accepted axiom closure is limited
to propext, Classical.choice and Quot.sound. No full-root build, remote CI,
publication or Git operation is claimed.
