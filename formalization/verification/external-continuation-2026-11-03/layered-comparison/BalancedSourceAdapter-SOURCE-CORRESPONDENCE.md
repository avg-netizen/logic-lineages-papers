# Balanced source payload to large-branch code

Source: paper08 `eq:balanced-atoms`, `thm:balanced`, `eq:balanced-row` and `eq:balanced-L`, specifically the literal source metadata and preceding-level affine labels used by the finite large-branch guard. The source file `08-multivariate-collapse-comparison/paper.tex` has SHA-256 `3c2bf4cb4d8b6145acf67ce14c3d818bd20c572b6547b07d57d8598b45940b25`. This adapter connects the accepted numeric source codec, accepted literal affine constructors and accepted finite postfix guard constructor. It does not implement induction on certificate levels or the full balanced comparison theorem.

## Exact original occurrence data

`BalancedEvaluation.upperData` is the existing total decode into `UpperData = Nat × List Nat × List AtomData`, and `AtomData = Nat × Nat × Nat × List Nat` is the existing stored outer coefficient, raw head code, offset and factor-list payload. `upperAtoms E F` concatenates the decoded left and right atom lists without changing any payload field. It retains full factor lists, offsets, stored outer coefficients, repeated heads and duplicate atoms in their original order. The first calibration equality is exact equality with `(E.atoms ++ F.atoms).map BalancedEvaluation.encodeAtom`, so preservation is not inferred merely from an evaluated value.

`coefficients E F` assigns `+(q+1)` to every original left occurrence and `-(q+1)` to every original right occurrence. The stored coefficient is never mistaken for the actual positive multiplier. Its order is exactly `BalancedLargeGuards.sourceCoefficients E F`, while `headCodes E F` is exactly `BalancedLargeGuardsCode.encodeHeads` of the head list from `BalancedLargeGuards.signedAtoms E F`. No sorting, grouping, deduplication or cancellation occurs in these maps. The list of raw atom payloads and the list of signed coefficients are separate because the coefficient's sign does not belong to a complete-input expression.

`originalConstant` is the signed difference of the two original natural constants. `outsideCoefficients k E F` contains exactly the `k` differences of the original outside coefficients, in basis order. On actual encodings these calibrate to `BalancedSyntax.comparisonRow E F`'s constant and remainder, respectively. A missing raw outside position defaults to zero and an excess position is ignored, consistently with the existing numeric source interface.

## Every component of the original threshold

The adapter computes the original row data before any equal-head/equal-input blocks can be collected:

- `coefficientMass`: the sum of the absolute values of all original signed coefficients, giving the source `C`.
- `outsideMaximum`: `BalancedRow.maximum` of the absolute values of all `k` signed outside coefficients, giving `C0`; an empty outside list has maximum zero.
- `factors k a`: the ascending `k`-entry list `storedFactor[j] + 1`, with a missing raw factor defaulting to stored zero, hence actual factor one. The original raw payload is not truncated or changed by this separate normalization.
- `multiplierMaximum`: `max 1` of the maximum over all such `k`-entry lists for all original atoms, giving `A`. In particular, an empty basis or an empty atom list gives one.
- `normOffset a`: the existing `rawNormCode` of the original head plus the original offset. `offsetMaximum` takes the maximum over every original atom, giving `B`.
- `normMaximum`: the maximum of the existing `rawNormCode` values of all original heads, giving `N`.

`threshold k E F` calls the accepted `BalancedNumerical.threshold` with the original signed constant and precisely those five budgets. Its literal value is `max 16 (max (2*C) (max (4*C0+4*|K|+4) (max (A+B+2) (N+2))))`. Each component, not only the final maximum, is calibrated to the corresponding accepted `BalancedRow` definition. The norm bridge is the already proved `rawNormCodeCorrect` together with `actualOrdinalNorm_notationCorrespondence`, not a supplied norm oracle. The `A` calculation uses every positive factor in every one of the `k` basis positions, including zeros in the stored representation, which denote one.

This original threshold and the full original signed coefficient/head lists are passed unchanged to `BalancedLargeGuardsCode.largeCode`. Bounds therefore cover every original occurrence, even an occurrence in a canceled block. No maximum or mass is recomputed from survivors, and no smaller post-cancellation threshold is substituted.

## Literal preceding-level labels under the same certificate

The numeric input includes `k`, the lower shape `Γ`, one original certificate code `C`, the two original expression codes and the desired integer sign. `lowerCertificate C` is exactly `(BalancedEvaluation.certificateData C).1`; on an actual source encoding it is `BalancedEvaluation.encodeCertificate Γ C.1`.

For every raw atom payload in `upperAtoms E F`, `termCodes k Γ C E F` calls the accepted `BalancedAffineCode.completeInput k Γ C (Encodable.encode a)`. For actual source atoms this is precisely the existing `encodeAtom (q,a)` payload, including its stored outer coefficient. That coefficient is retained in the payload but does not affect `completeInput`. Both signs use the same original `C`; there is no synthetic signed coefficient in the affine input, no separate basis and no fresh variable for a basis entry.

After all original complete inputs, the list appends `BalancedAffineCode.lowerPart k Γ C E` and `BalancedAffineCode.lowerPart k Γ C F`, in that order. `ExactLiteralSourceLabels` requires exact equality with `BalancedLargeGuards.sourceTerms k Γ C E F` mapped through `BalancedEvaluation.encodeSyntax Γ`. Thus its first `m` labels name the original complete inputs and labels `m`, `m+1` name the literal left and right outside expressions. The calibration includes the BASE lower shape `Γ = []`, repeated or dependent basis entries, shared raw variables and zero outside coefficients.

## Exact assembled result and ambient support

The output is the tuple `Nat × List Nat × BalancedLargeGuardsCode.Code`: lower-certificate code, ordered literal lower-term codes, then the existing eight-tag postfix formula code. `ExactAssembledSourceCode` requires both the formula-code equality and the whole tuple equality with the semantic source construction. The formula is exactly `CommonHeadCompiler.encode (BalancedLargeGuards.sourceFormula E F desired)`, not merely an equivalent formula or a stream with simplified neutral instructions.

The lower shape `Γ` remains an explicit input to every term construction. The caller also retains the original pair's ambient raw-variable support, as already defined by `BalancedLargeGuards.sourceAmbient k Γ C E F`. This adapter does not discard that source context or replace its support by variables surviving fixed-head simplification or block cancellation. No claim that the guard's support equals the original support is introduced. No runtime equivalence is bundled into the target: exact term/certificate/formula code equalities connect directly to the accepted semantic and runtime suppliers without broadening this component.

## Four exact targets and numeric totality

1. `ExactOriginalMetadata`: original atom payload preservation, signed coefficients, ordered encoded heads, signed constant, entire outside row, each of the five budgets and the original threshold.
2. `ExactLiteralSourceLabels`: exact encoded `C.1` and exact ordered encodings of the accepted source terms.
3. `ExactAssembledSourceCode`: exact accepted postfix source-formula code and exact full three-component result.
4. `UniformPrimitiveRecursive`: all seventeen numeric maps, uniformly on arbitrary finite numeric inputs, including the full shape and certificate code.

The seventeen maps are `upperAtoms`, `coefficients`, `headCodes`, `originalConstant`, `outsideCoefficients`, `factors`, `normOffset`, `coefficientMass`, `outsideMaximum`, `multiplierMaximum`, `offsetMaximum`, `normMaximum`, `threshold`, `lowerCertificate`, `termCodes`, `formulaCode` and `assemble`. Uniformity is not restricted to a fixed shape, a fixed certificate, a finite set of heads or valid source codes.

Failed upper and certificate decodes use the accepted defaults `(0,[],[])` and `(0,[])`. Existing list access defaults apply to missing raw basis codes, factors and outside coefficients. The original stored payload lists remain intact. Raw head codes use the existing total `rawNormCode` and the accepted `largeCode` constructor's existing raw comparison behavior. Malformed inputs are total numeric inputs to these maps, not a claim of source validity, normality or semantic correctness for malformed encodings.

The anticipated primitive-recursion suppliers are `BalancedEvaluation.Program.upperData_primitive` and `certificateData_primitive`, the accepted `BalancedAffineCode.Proof.uniformPrimitiveRecursive`, the accepted `BalancedLargeGuardsCode.Proof.uniformPrimitiveRecursive`, and `rawNormCodePrimitiveRecursive`. The ordinary numeric operations are integer coercion/subtraction/negation/absolute value, natural addition/multiplication/maximum, existing list codecs, map, append, range, flatMap, sum and fold. No head evaluator, raw valuation, source evaluator, comparison oracle or assumed effectiveness certificate is an input. The semantic calibration needs no genuine-limit-head premise, because it compares literal codes and actual normal-notation norms rather than proving the large-branch sign theorem afresh.

## Deliberate boundary and draft state

This component does not compile guards recursively at the lower certificate, enumerate small-input exceptions, evaluate source rows, prove exact translated free-variable equality, supply a full balanced compiler or invoke Snyatkov. The paper's full numbered theorem remains pending until those obligations are met.

Only new definitions, four target propositions, exact statement-check aliases, this correspondence and a freeze specification are drafted. `BalancedSourceAdapterSemanticProof.lean`, `BalancedSourceAdapterDataProgramsProof.lean`, `BalancedSourceAdapterProgramsProof.lean` and `BalancedSourceAdapterProof.lean` are deliberately absent. Root exact review, comparator compilation and freeze are required before authoring candidate proofs. No compiler, proof authoring, Git operation or accepted-file edit was performed as part of this draft.
