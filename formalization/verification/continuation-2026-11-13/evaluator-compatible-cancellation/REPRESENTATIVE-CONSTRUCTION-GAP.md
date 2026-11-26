# Concrete retained-representative construction audit

Read-only mathematics audit; no new target or representative is selected.

## Exact source path

`GlobalSourcePackageProof.actualOriginalGlobalInputSelection` selects its base via `InternalOriginalUniformDescentSelectionProof.actualOriginalUniformDescentSelection`, which obtains four leaves from `InternalOriginalUniformParameterLeavesProof.actualOriginalUniformLeafPrograms`.

The latter obtains oldRepresentative through `GorbowPRProgram.Proof.allPrimitiveFunctions 2 _ (representativePrimitive n arity)`. This is a genuine constructive existential Program witness, not an axiom and not a named transparent representative AST. The private `GorbowPRProgramProof.programOfTextbook` constructs zero/succ/projection/composition/recursion witnesses by induction on `Nat.Primrec'`, selecting a family of component witnesses in the composition case. Its public output is existence plus native evaluate equality, not an internal structural graph specification.

## Native contract

`InternalOriginalUniformParameterLeaves.Calibrated` gives all-vector evaluate equality to `representativeValue`, including malformed/default behavior. That value decodes the original context and Object parameter, performs original rawPackedDecode, maps the resulting packed term through `ContextUniformPrimary.representative`, and defaults to zero on failed decoding.

The native representative computes original bounded candidates, finite exchange reachability, then bounded least-code findIdx. Exact native correspondence is `InternalOriginalUniformParameterLeavesCalibrationProof.representativeCalibration`, using `ContextUniformPrimaryCalibrationProof.actualRawRepresentativeCalibration`, to `InternalQuotientEdgeChecker.targetRepresentativeValue`. No successful-input-only scope replacement is justified.

## Same leaf retained

`EvaluatorKeyPut.baseRepresentative` is `(ObservedPut.prepared p H G W).base.oldRepresentative`. `PutIntegration.seed` installs PUT only in oldStep after transparent validity leaves. `OriginalMixedPrepared.prepared` again applies transparent validity replacement, direct-bottom oldStep refinement and mixed-path oldStep refinement. All preserve the original oldRepresentative field literally. This leaf is not `InternalOriginalUniformDescentSelection.representative` (the fallback bounded normalizer) and not the later NEW minimum.

## What is and is not internally exported

Original descent selection also proves source/target validity, typed factorization, fallback-normalizer output validity/type/fixedness, typed output and source application closure. These are generic in the retained leaf; they do not expose the compiled representative's primary-class computation or establish its E-fibre compatibility.

The smallest construction-facing missing interface is an internal source-restricted structural graph characterization/congruence for this same compiled primary-class least-code witness, with compiler provenance preserved. No such contract is exported along the inspected selection path. Merely rewriting using native evaluate equality would be an invalid native-to-internal inference. Even after establishing such a characterization, an E-to-original-primary-class bridge would still need proof; it is not silently paid by calibration or rank determinacy.

This is not an impossibility claim or a refutation of calibrated compatibility. It does not authorize a new tuple or replace the accepted conditional rule. Source hashes accompany this audit so the inspected construction can be recovered exactly.
