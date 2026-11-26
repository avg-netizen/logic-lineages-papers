# Bounded strict-edge transport scope

Source thm:cut, paragraph “Transport of strict multiset occurrences.” Preliminary complete three edge families, not cut itself. `Below S n` is precisely the intended primary strong-induction hypothesis: it requires a concrete right WeakTree with count < n and Ordinary final endpoint, while permitting arbitrary left E evidence. The three endpoints each take a concrete right strict/weak tree whose own count is < n; strict cases use its actual weak child and prove the strict count inequality internally. No unbounded relation composition parameter is introduced.

Weak–strict: invert actual right strict tree, use checked markability reflection on left E, total marking transport, and equality of successful partial marking with total headmark, then Below on the actual right child. Original source/target PaperTerm at the same type follows from endpoints and annotation preservation.

Strict–weak: invert actual left strict witness, keep its successful mark and use Below directly on actual right weak tree. Strict–strict: invert both strict witnesses, mark-transport the left marked-result-to-intermediate edge; successful marked result is fixed by total marking. Apply Below to the actual right weak child, then reconstruct original left strict mark.

This helper scope never drops Ordinary c. Final theorem will have to supply Below from primary induction; no acceptance of any unbounded cut follows here. Actual matching/multiset occurrence partition construction remains separate and will get its own complete frozen scope.
