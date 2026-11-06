# Semantic review: literal outer-shift normalization

Independent read-only review accepted the original frozen comparator and the separately frozen additive leaf/word comparator before their candidate proofs. The original Definitions/Targets were not changed when the complementary scalar leaf/word target was added. Both comparator sets had their own successful native preflight.

## Literal syntax and domains

`splitSyntax` proves that the original word is exactly the computed core followed by its computed maximal all-shift suffix. The core is either empty or ends at an original non-shift occurrence. It is empty exactly when every original letter is a shift. All unused fields and order are preserved in the literal decomposition.

`normalizationSyntax` retains degree admission, E count and every positive-rank range count. Rank zero includes both shifts and counters, so it is excluded from the range invariant; E occurrences have their own unchanged count. No dropped nonlinear occurrence or duplicate argument is hidden in the normalization.

`shiftSumCorrect` inducts through the original successive domains. At each signed shift, nonnegativity of that actual input plus index justifies casting `toNat` back to the exact integer. This proves the final integer sum without treating truncated negative inputs as valid.

`normalizationCorrect` uses the exact original decomposition and append-domain law. It keeps the original core domain, proves the combined outer shift is nonnegative from the actual original final value, and obtains identical normalized and original values. It deliberately gives no converse from the normalized domain to all original intermediate domains. `tailNormalization` separately pays the original `wordTail` to establish both domains effectively.

## Terminal comparisons

All-shift/all-shift strict, equality and weak comparisons reduce to integer-linear expressions in the unchanged raw inputs. Empty words and arbitrary unused shift fields are included.

The additive leaf/word comparator proves a scalar view with the first input occurring only linearly and all original domains paid. It is not a formula compiler and does not distinguish raw variable names. In the same-variable case, leaf sums or the nonlinear-growth result must decide the comparison; this scalar view is not used to claim an atom x<W(x) is linear.

`nonlinearLeafGuard` applies the accepted original-source terminal growth result at the actual signed sum of an arbitrary all-shift opposite word, then transfers its exact value from the paid original domain. The cutoff also pays the original opposite word tail. The source restriction y≤x and all original variables are retained.

All split/sum/normalized-word and cutoff maps are the actual primitive-recursive programs, not effectiveness assumptions. Complete guard recursion and ordinal termination, a general same-variable word decision algorithm, ranked row cancellation and first-order BASE remain pending. The source register is unchanged.
