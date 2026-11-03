# Balanced large-branch numeric guard construction

Source: paper08 `thm:balanced`, `eq:balanced-row`, `eq:balanced-L`, specifically the finite guarded-preorder construction on the large branch. The source file `08-multivariate-collapse-comparison/paper.tex` has SHA-256 `3c2bf4cb4d8b6145acf67ce14c3d818bd20c572b6547b07d57d8598b45940b25`. This component supplies a uniform numeric implementation of the already accepted `BalancedLargeGuards` formulas. It does not replace their source semantics, threshold, source labels or preceding-level certificate.

## Raw inputs and fixed heads

The constructor receives a finite raw head-code list, a finite signed integer coefficient list, a natural threshold and an arbitrary desired integer sign. Each original occurrence is still identified by its zero-based coefficient-list position. The lists need not have equal lengths. Head positions beyond the supplied list use raw code zero; excess head entries are unused except when an explicitly supplied key or mask label names them. `encodeHeads` maps a list of actual normal `NONote` heads to their literal `rawNoteEncode` codes in the original order, retaining repetitions. It is a calibration map, not a new codec or a numeric oracle.

`ExactHeadsAndKeys` explicitly requires that actual normal zero has raw code zero and that raw lookup commutes with `List.getD ... 0` at every index, including absent labels. Thus both sides of every later calibration use the same total head function `fun i => heads.getD i 0`. No in-range premise or hidden length agreement is added.

Fixed head equality is numeric equality of their faithful raw codes. Fixed strict head order is `rawComparisonCode a b = 0`, never `a < b`. The target calibrates this comparator both to literal `ONote.cmp` and to actual ordinal representation order on normal heads. Existing suppliers are `rawComparisonCorrect`, `rawComparisonOrdinalCorrect`, `rawComparisonPrimitiveRecursive` in `RawComparisonProof.lean`, and the faithful roundtrips in `RawNotationCode.lean`. The identifiers `actualONote`, `actualNONote` and `CommonHeadCompilerProgramProof` are not present in this checkout; no substitute dependency with one of those names is introduced.

Equal heads emit the original input-label equality or order instruction. An earlier fixed head emits truth for a key-order test; a later unequal head emits false. The generated instruction stream contains no head-evaluation or ordinal-comparison opcode. Head comparison happens numerically during construction.

## Exact finite instruction lists

The output is precisely `List CommonHeadCompiler.Instruction`, using the existing postfix tags: 0 false, 1 true, 2 equality, 3 strict input order, 4 lower bound, 5 negation, 6 conjunction, 7 disjunction. Existing `CommonHeadCode` constructors append their operand codes and then the operator instruction. `conjoin` and `disjoin` are the existing right folds with explicit final truth and false instructions, respectively. These neutral instructions are retained even for nonempty lists, so the target is exact list equality with `CommonHeadCompiler.encode`, not an optimization or merely truth-value equivalence.

Every guard over occurrences maps `List.range m` in ascending order. Every mask is the unchanged Boolean mask from `CommonHeadLargeGuards.masks`: length zero gives `[[]]`; length `n+1` gives all `false :: mask` values in the previous order, followed by all `true :: mask` values in that order. At length two this is `[[false,false],[false,true],[true,false],[true,true]]`. Stable filtering retains precisely those masks whose full signed coefficient sum has the requested sign. No sorting, deduplication, coefficient cancellation or omission of original occurrences changes any list. An arbitrary mask's missing bits default to false and extra bits are ignored by `maskCode`; masks generated for `blockCode` have the coefficient-list length. The inherited `maskCoefficient` uses its literal signed `zipWith` sum.

For each mask, positive and negative head-and-input membership guards occur in the original index order. `canceledCode` tests all blocks in that order. `maximalCode` requires every strictly greater actual key to cancel. It selects greatest surviving blocks rather than assuming the greatest original key survives. The final disjunction ranges over every original occurrence, retaining duplicate candidate blocks exactly as the semantic formula does.

`differenceSignCode` uses the two original final labels `m` and `m+1`, in left/right order; desired values outside `{-1,0,1}` emit false. `signCode` places the all-canceled lower-expression branch first and the surviving-block branch second. `largeCode` places the conjunction of all original occurrence bounds first and the sign formula second. The original threshold is supplied unchanged; it is not recomputed after collection. Empty rows, negative and zero coefficients, repeated heads and arbitrary desired integers are all covered.

## Four exact targets and effectiveness

1. `ExactHeadsAndKeys`: faithful total default lookup, actual fixed-head comparison, and exact postfix equality for the two key formulas.
2. `ExactFiniteGuardCode`: exact postfix equality for masks, signed blocks, all-canceled and maximal-survivor guards.
3. `ExactLargeGuardCode`: exact postfix equality for lower differences, sign formulas and `BalancedLargeGuards.largeFormula L (fun i => heads.getD i 0) cs desired`.
4. `UniformPrimitiveRecursive`: genuine uniform primitive recursion for all ten new numeric maps on arbitrary finite raw inputs, with no normality or source-validity premise.

The primitive-recursion proof can reuse the checked public `CommonHeadCode.Program` facts in `CommonHeadCodePrimitiveProof.lean`: `constant_primitive`, `conjunction_primitive`, `disjunction_primitive`, `negative_primitive`, `conjoin_primitive`, `disjoin_primitive`, `masks_primitive`, and `coefficient_primitive`. The latter two already prove the required mask enumeration and signed summation effective. `CommonHeadGuardProgramsProof.lean` supplies the matching existing map/filter construction pattern, and `IntegerAlgorithms.Proof.sign_primitive` supplies the actual integer sign operation. Ordinary primitive-recursive list lookup, map, range and stable filter combine these with the checked raw comparator. No ordinal evaluation, source valuation, arbitrary comparator parameter or precomputed comparison table is an input to a new map.

The exact calibration quantifies over arbitrary finite lists of normal heads, not only limit heads. Malformed raw inputs still have total numerical programs and the same primitive-recursion guarantee; they are not asserted to encode normal heads or a valid source expression. All semantic source validity remains with the accepted source layer.

## Deliberate boundary and draft state

This component does not extract source atom payloads, compute the original source threshold, build complete-input or lower-part syntax codes, combine source labels with the postfix runtime, enumerate small exceptions, recurse on certificate levels, prove full translated free-variable equality or invoke Snyatkov. Those later adapters and compiler obligations remain pending. In particular it does not assert a full raw balanced comparison compiler.

Only the definitions, four target propositions, exact statement-check aliases, correspondence and freeze specification are drafted here. `BalancedLargeGuardsCodeSemanticProof.lean`, `BalancedLargeGuardsCodeProgramsProof.lean` and `BalancedLargeGuardsCodeProof.lean` are deliberately absent. Root exact review, comparator compilation and freeze must precede authoring them. No Lean command, candidate proof, Git operation or accepted-file edit belongs to this draft.
