# Remaining recognition-factor bridge (not proved)

Desired separate exact theorem: for the same S and fixed NEW C/L, actual recognizes(S,C)=1 at (s,t,cert,param) implies actual recognizes(S,L)=1 at the identical tuple. The checked `OriginalMixedClosedFactorProof.actualRawFactor` only strips C acceptance to L acceptance at one tuple; it does not prove recognition transfer or equality of transition Programs.

## Why this is plausible but needs proof

Each recognizer hop is guard AND leaf. The branch structure checks lambda first, then application-function. Successful lambda under C remains successful under L. Successful application under C supplies C=1 and the application guard. `OriginalTransparentApplicationFunctionInverseTagProof.sourceTag` recovers source tag2; `OriginalTransparentMixedPathApplicationControlProof.lambdaGuardReject` rejects the lambda guard at that SAME tuple. Thus switching leaf C to L cannot promote the lambda branch on that application step. This disjointness must actually be used; `choiceRecover` returns only a disjunction of accepted branches and discards the failed earlier test.

There is an alternative generic argument only if the old earlier-test rejection is retained: C=1 together with not(guard1 AND C)=1 implies guard1 rejection, hence rejection of guard1 AND L. This relies on both tests using the identical shared leaf factor. It is not arbitrary monotonicity of priority branching.

## Existing exact building blocks

* `OriginalMixedClosedFactorProof.factor` and actualRawFactor: C acceptance -> L acceptance at actual four inputs, no native reflection.
* `OriginalMixedDirectBottomTraceDescentProof.acceptingRunNonzero`: an actual run with accepting finish cannot start at zero.
* `OriginalMixedDirectBottomTraceDescentProof.actualFrontDescent`: on actual original cons(path,head,tail), extracts selected accepted hop plus actual childLive and accepting tail run; branch rejection is not in its conclusion.
* `OriginalMixedDirectBottomTraceFrontQueryProof.frontCases`: exposes actual state/next/out and selected branch information at original tuple.
* `OriginalTransparentApplicationFunctionInverseTagProof.sourceTag` and `OriginalTransparentMixedPathApplicationControlProof.lambdaGuardReject`: genuine application/lambda exclusion. `applicationAtLive` belongs to the normalization transition and is NOT directly a theorem about the trace recognizer transition; use its branch algebra as a model, not an unchecked rewrite.
* `OriginalMixedDirectBottomTraceProof.repeatNil/repeatFront`, and `InternalRawListRepeatProof.frontConsForward/frontConsBackward`: original raw-path recursion laws.
* `OriginalHereditaryLambdaChildStateProof.atLiveRecover`: actual four-field guard and leaf recovery. Terminal is sourceAt S AND (leaf AND DirectBottom.active), so accepted terminal C transfers by factor with all other fields unchanged.

## Required new proofs

1. One-step selected trace transition simulation at actual live state, C-accepted selected node, preserving the SAME next state. Pay lambda-first priority explicitly in the application branch.
2. Terminal finish acceptance transfer at the SAME actual final state. Query state coordinates if not already live; do not infer native state decoding.
3. Internal original-path induction for an ACCEPTING run: repeat(transition C,out,path,state) AND finish C(out)=1 implies existence of the SAME out run with transition L and finish L(out)=1. Nil uses terminal transfer; cons uses accepted-tail nonzero, selected-step simulation, actual tail IH, frontConsBackward.
4. Expose initial path/live/run queries of recognizes C, apply (3), then compose recognizes L. All state, certificate, and parameter coordinates remain unchanged.

A global all-state transition graph equality is false in general: rejected C states may still satisfy L and select a nonzero hop. A generic unconditional repeat-congruence theorem therefore cannot be applied. This bridge was assessed before the cutoff, but no target/proof has been claimed or added; the several new internal simulation/induction steps should be frozen and checked in a subsequent continuation.
