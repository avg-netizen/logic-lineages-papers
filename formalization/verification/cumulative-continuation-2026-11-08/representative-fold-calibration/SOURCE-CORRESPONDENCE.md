# Original representative fold: external calibration

This is a three-target supporting packet for paper 06, `lem:id1`. It connects
the existing bounded result fold and its independent payload-recursive
semantics to the original least-code representative functions. It does not
assert an internal application congruence or close the arithmetic accessibility
proof. No numbered source statement changes status.

## Original source and fixed window

`06-godel-t-termination-ordering/paper.tex`, lines 537–549, fixes a finite
subtype-closed type window and the original auxiliary application rule.
Lines 551–556 fix the original finite primary equivalence classes and their
least-code representatives. Lines 558–560 state the supporting ID1 lemma.

The semantic and concrete-fold calibration targets explicitly assume
`SubtypeClosed (fun tau => tau ∈ S)`. The final target selects programs
for each fixed window, retaining the exact old Data when closure does not
hold. It is existential selection, not a uniform effective compiler in S.
The context Gamma, arities, symbols, window and step table are the original
parameters. No precedence, target-universe or successful-input-decode premise
is added. The original calibrated validity and representative leaves are
supplied as before; this packet does not prove their existence from scratch.

## Frozen concrete AST contract

All programs are ordinary finite `GorbowPRProgram.Program` syntax. The new
Data has no proof fields and the existing fold, state machine, codecs and
fuel are unchanged. The following exact definitions must also be used by a
later internal fold-constructor packet; they may not be replaced by merely
extensionally equal programs without a separate internal proof.

1. `rootGuard validity member` is exactly
   `(InternalApplicationValidityStack.recursiveData validity member).sourceValid`.
   The generic fold opens a visit only when the original raw constructor tag
   is two AND this guard on the WHOLE RAW ROOT returns exactly one. A target
   decoder, codomain-membership test alone or already-normalized child cannot
   replace that root guard.
2. `leaf validity member old` is exactly the already checked
   `InternalRepresentativeTag.representative` wrapper around the recursive
   target-validity AST and `old.targetRepresentative`. It returns zero on
   failed packed decoding. On successful decoding it pairs the raw input's
   outer tag with the old target representative's payload. The checked tag
   wrapper calibration preserves the original target representative on EVERY
   natural input and EVERY window, including packed terms outside the universe.
3. `combine old` reads exactly `[d,e,f,a]`, where f and a are whole computed
   packed child outputs. It returns
   `pair e (right (old.targetRepresentative (rawApplication d e f a)))`.
   Here the ORIGINAL raw application is
   `pair e (pair 2 (pair d (pair (right f) (right a))))`.
   The outer pair is explicit syntax. Its tag is e even for off-domain
   combine inputs. We do NOT claim that this standalone combine agrees with
   the old target representative on arbitrary malformed applications: only
   the complete guarded fold is calibrated.
4. `normalizer validity member old` is exactly
   `InternalApplicationResultStack.fold rootGuard leaf combine`, with the
   existing `2 * originalPayload + 1` fuel and unbounded computed outputs.
5. `foldedData` literally preserves `old.stepProgram`. Its source program
   returns the normalizer when the exact rootGuard returns one and zero
   otherwise. Its target program is the normalizer on every natural input.
   The source test uses the existing exact-one AST, not generic nonzero truth.

The input coordinate order, output pair, source guard, target leaf and
unchanged step field are frozen in Definitions before proof authorship.

## Three exact obligations

1. `ActualOriginalSemanticRepresentativeFoldCalibration` equates the
   independent `semanticFold` using the evaluations of those exact three
   programs with the ORIGINAL `targetRepresentativeValue`, for every raw
   natural input under subtype closure and the original leaf calibrations.
   The right-hand side is unchanged packed decoding followed by the original
   least representative, or zero on failed decoding. It is not a new
   recursive definition engineered to satisfy the fold equation.
2. `ActualOriginalRepresentativeFoldProgramCalibration` proves the existing
   full `InternalQuotientEdgeChecker.Calibrated` contract for the concrete
   `foldedData`. This includes the unchanged step program and BOTH complete
   source/target all-input equations. It must consume the generic result
   fold calibration as an established theorem. Generic calibration is not
   an extra implication premise or a field of the selected Data.
3. `ActualOriginalFixedWindowRepresentativeSelection` gives calibrated Data
   for each fixed S, with equality to the literal `foldedData` when S is
   subtype closed and equality to the literal old Data otherwise. It makes
   no claim that the recursive normalizer calibrates bad windows and provides
   no uniform compiler or decidability result for subtype closure.

## Supplier boundaries and required source argument

The generic result-fold packet was separately frozen and is still being
proved at this freeze. Its actual target is
`InternalApplicationResultFoldCalibrationTargets.ActualOriginalBoundedResultFoldCalibration`.
It must pass its own exact gate before the concrete representative program
calibration can be accepted. No in-progress proof source is pinned as an
accepted supplier in this packet. The shared semantic definition and generic
Targets/Preflight bytes are pinned as specification, not as a proof receipt.

The original recursive-validity calibration is already checked. It provides
exactly the old source-universe and packed-target validity functions, on all
inputs and without a closure premise. The checked representative-tag wrapper
preserves the old target behavior at every fallback leaf. The checked payload
bound justifies recursion on the original term payload, not the reconstructed
packed code or output size.

At a source-valid opened application root, the source application decoder
and `sourceAppAcceptance` establish both original typed child decodes and
both child-universe facts. The original decoded-representative supplier
`NumberedNumericApplicationSupportProof.decodedRepresentative` supplies
correctly typed universe representatives for each child. The original
`NumberedQuotientApplicationProof.representativeApplicationCongruence`, with
its explicit subtype-closure and four universe premises, relates the
application of those representatives to the original application. Original
packed decoding and outer-type preservation justify the explicit codomain
repacking in combine. No application congruence is applied outside this
valid opened-root branch.

The semantic proof must induct on original payload. Both child payloads
strictly decrease by the checked original application bound, while computed
representatives can grow without restriction. At a nonapplication root, or
any root whose source-universe guard is not one, the semantic fold returns
the original target leaf on the WHOLE unchanged raw input. This covers valid
packed targets outside the universe, arbitrary malformed inputs and failed
decodes without silently strengthening target validity.

The source projection of the concrete Data uses source validity only at the
outer input. On source acceptance, the old source and old target values are
the same original representative. On source rejection, the old source value
is zero while the target continues to retain its distinct packed-decoder
behavior. The target has no newly inserted universe filter.

## Exclusions and admission state

These are EXTERNAL standard-natural-number calibration targets. There is no
reflection of evaluation truth into internal `Derivation`, no internal graph
congruence premise, no internal fold constructor theorem, and no claim that
semantically equal programs are interchangeable inside the calculus.

Internal representative application congruence, typed application-step
integration, the certified application lift, context-uniform representative
compilation, outer malformed-object handling, the source multiset/lambda
arguments and the closed all-term ID1 endpoint remain separate obligations.

At this freeze, no proof author or compiler has started for this packet.
Independent review and native preflight must precede target authorship. No
Git action, publication, full-root build, or remote CI result is claimed.
