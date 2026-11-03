# Balanced actual-support small-box supplier

Source: paper08 `thm:balanced`, specifically `08-multivariate-collapse-comparison/paper.tex` lines 1007–1022, together with the original balanced grammar and threshold at lines 947–980. The positive raw-variable domain is explicit at lines 47, 833 and 848. The source file has SHA-256 `3c2bf4cb4d8b6145acf67ce14c3d818bd20c572b6547b07d57d8598b45940b25`. This component supplies actual-support stability, the small-input bound and exact finite positive representatives. It does not yet filter the finite box by comparison sign, build its point formula or claim the effective balanced translation.

## Original support, original inputs and original threshold

`sourceAmbient k Γ C E F` is literally `BalancedSyntax.rawVariables (k :: Γ) C E ++ BalancedSyntax.rawVariables (k :: Γ) C F`. It is the same original-pair list used by the accepted large-guard component, not the support of a simplified guard or a collected row. The existing source support removes zero outside multiples and includes the entire common basis support for each listed positive atom. Original occurrences remain represented even when their signed blocks later cancel.

`sourceSupport` deduplicates this list only to choose one coordinate per raw variable name. It never deduplicates basis entries or gives them independent values. The original `C : Certificate (k :: Γ)`, its lower certificate `C.1` and all its ordered basis entries `C.2 j` are retained. `basisSupport` separately lists the raw support of every one of those entries, with repeated names allowed.

`completeInputs` maps the original `comparisonRow E F` atom list to `BalancedRow.input (basisValues k Γ C ν) a.2`. The result therefore contains every original left and right occurrence in source order, including duplicate atoms and occurrences whose eventual collected coefficient is zero. These are the complete norm inputs `N(λ) + offset + Σ_j (storedFactor_j + 1) B_j`, not merely the arguments passed after removing the head norm.

`originalThreshold E F` is exactly `BalancedRow.threshold (comparisonRow E F)`. `smallBranch` asserts that one atom in that original row has a complete input strictly below this exact threshold. It is false for a head-free row. No threshold is recalculated after cancellation and no larger substitute bound is introduced. The representative target writes `BalancedRow.threshold (comparisonRow E F)` explicitly in its word-membership conclusion.

## Actual source stability, without restrictions outside support

`ActualSourceSupportStability` says that two arbitrary functions `ν μ : Nat → Nat` agreeing on `sourceAmbient` give equal actual values to both original source expressions and equal ordered lists of all complete inputs. When the original row has an atom, the whole ordered `basisValues` list also agrees. No genuine-head, positivity or independent-basis premise occurs in this target.

The conditional basis conclusion is deliberate. If an original atom exists, every common basis entry occurs positively in that atom, so all its raw names are visible in the ambient pair support. If neither side has an atom, unused basis entries need not appear in either source expression. Claiming unconditional equality of all basis values from original-support agreement would be false in that case. The complete-input list is empty there, and the two actual source values still depend only on their actual outside supports.

## The exact small-input bound

`ActualSmallInputBounds` assumes only `genuineCertificate (k :: Γ) C` and `smallBranch k Γ C E F ν`. It concludes that the original basis sum is less than original `L`, that every original basis value is less than `L`, that every raw name in any basis entry has value less than `L`, and that every name in the original ambient support has value less than `L`.

The basis sum bound uses positive factors in the original complete input: `Σ_j B_j ≤ t_i < L`. Each basis value is bounded by the sum. The actual-support domination supplier applies recursively to each genuine lower expression `C.2 j`. Every name occurring in either source expression lies in the common basis support, including a name used only by the outside remainder. The small-branch atom also ensures the entire basis is visible in the original ambient support. This is the paper's whole-pair basis condition, not a bound only on head-local or surviving support.

No top-level `genuineExpression E` or `genuineExpression F` premise is needed for this bound. The top-level heads contribute nonnegative norm offsets but are not evaluated in the bound; genuine heads are required recursively where support domination evaluates lower-certificate expressions. Positivity of `ν` is also unnecessary for these upper bounds. It is required only on actual ambient raw names when selecting a word in the positive box.

## Existing finite words and lookup, without a new encoding

The component imports `SingleCorePresburgerDefinitions` and uses the existing `singleCoreBoxWords` and `singleCoreBoxLookup` literally. It does not define a replacement encoding, convert source values to shifted coordinates or silently substitute zero. `boxWords` uses the original threshold and the length of the deduplicated actual support. `boxValuation` uses the accepted first-occurrence lookup with default one.

`ExactFiniteBox` specifies five elementary facts about those existing functions:

1. Membership in `singleCoreBoxWords L n` is equivalent to length `n` and every coordinate satisfying `0 < v ∧ v < L`.
2. At length zero, the enumeration is exactly `[[]]` for every `L`, including `L = 0` and `L = 1`.
3. Looking up a variable in `support.map ν` returns `ν` on every member of `support`, even when a generic support list repeats names.
4. If word and support lengths agree, lookup is one outside support. The length premise is necessary for the existing `getD` definition and is not omitted.
5. Every enumerated word produces a globally positive lookup function whose values on support are less than `L`.

For the actual source box, `sourceSupport` has one coordinate per raw name by its literal `List.dedup` definition. The exact membership law gives the full finite box `[1,L-1]^V`; it does not introduce arbitrary independent values for basis expressions. The empty-support box consists of the single empty valuation, represented by the globally-one function. No equality-point guard or exact formula free-variable claim is included in this supplier.

## Canonical positive representative

`ExactSmallBranchRepresentative` assumes a genuine shared certificate, positivity of `ν` only on `sourceAmbient`, and the original small branch. It gives a word equal to `(sourceSupport k Γ C E F).map ν`, membership in the existing enumeration at `BalancedRow.threshold (comparisonRow E F)`, agreement of its lookup with `ν` on every original ambient name, global positivity of that lookup and its exact default one outside ambient support. Both actual source values and the complete ordered input list are preserved, and the representative still satisfies the original small branch.

There is no premise on `ν i` when `i` is outside actual support. Those values may be zero, exceed `L` or differ arbitrarily from the representative. Replacing them by one is justified by support stability, not by restricting the original valuation or claiming that an outside coordinate belonged to the finite box. In particular the positive-source theorem can later apply to the representative without changing either source value or any branch input.

## Proof dependency plan and exact boundary

The accepted `BalancedSyntaxSupportProof` already states actual-support stability and domination, but its import through `BalancedSyntaxRowProof` reaches `BaseTermProgramInterfacesProof` and a broad linked-residue closure. No accepted import is edited here. After the exact comparator is compiled and frozen, a new thin support candidate may prove the elementary required facts locally using `BaseTermProgramsProof`, `HeterogeneousHeadProof` and `BalancedBasisProof`, with any needed finite-basis list lemmas in the new candidate. Likewise the accepted `SingleCoreBoxProof` imports the heavy single-core evaluation proof; a thin new finite-list candidate may prove the relevant existing words/lookup laws directly without that evaluator dependency. `SingleCorePresburgerDefinitions` itself has no `LinkedResidue`, `BaseTermProgramInterfacesProof` or `SingleCoreEvaluationProof` in its local import closure.

The four targets are `ActualSourceSupportStability`, `ActualSmallInputBounds`, `ExactFiniteBox` and `ExactSmallBranchRepresentative`. These are semantic suppliers. There is no source evaluator algorithm, numeric uniform computability target, runtime validity oracle, finite sign filter, small-point formula, raw compiler, recursively compiled balanced comparison or invocation of Snyatkov in this component. The full numbered `thm:balanced` remains pending.

Only definitions, four target propositions, exact statement-check aliases, this correspondence and the freeze specification are drafted. The four candidate files are deliberately absent: `BalancedSmallBoxSupportProof.lean`, `BalancedSmallBoxBoundsProof.lean`, `BalancedSmallBoxFiniteProof.lean` and `BalancedSmallBoxProof.lean`. Comparator compilation, exact root review and freeze must precede candidate authorship. No compiler, proof authoring, Git operation or accepted-file edit was performed for this draft.
