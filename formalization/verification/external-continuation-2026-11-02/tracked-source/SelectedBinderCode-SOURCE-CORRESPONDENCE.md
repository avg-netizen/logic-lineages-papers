# Numeric capture-avoiding selected-binder permutation

Paper 09 common-unit elimination and the effective head-graph construction use actual typed source transformations before building the finite observation tree. The existing UnitElimination.step explicitly renames the selected functional entry to the context head. Its typed SelectedBinder.moveToHead/index/naturality theorems are established, but raw numeric construction was not supplied by the insertion or single-deletion codecs.

The exact source target covers arbitrary source terms, types and protected prefixes. Below that prefix, old indices before the selected slot increase by one, the selected slot becomes zero, and later old indices remain unchanged. Every internal lambda increments protected depth, regardless of its type. Literal source constructors and annotations are preserved. The ordinal and complete-vector targets retain every component coordinate and vector entry.

The algorithms are uniformly primitive recursive in depth, selected index and literal code, including explicit malformed-code totalization. Correctness and actual assignment claims concern typed inputs; no validity is inferred for malformed inputs. The last target derives a whole original assignment and calibrates the actual numeric assignment of the permuted source.

This component does not implement the context selector, OneUnit compiler, UnitElimination tree compiler, or whole effective head graph. It does not merge private names or substitute independent values for shared inputs.
