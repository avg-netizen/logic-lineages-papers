# One exact normalized ordered list of arbitrary fixed-head wires

Paper 17, `17-permitted-control-canonical-comparison/sections/arithmetic.tex`, lines 3–27 and 33–48. This aggregates the original one-gate wire normalization #976 with no change to its reader.

- Normalize each original canonical head in order: finite is one original natural affine wire, infinite is one proper original limit-collapse pair on the same source/output wires with the exact transported hidden norm input. The normalized list preserves order and occurrences.
- The caller supplies globally distinct infinite hidden names, disjoint from every original source/output name. The finite branch never allocates its dummy hidden field. The original wires may repeat freely or serve as shared graph nodes. No original output is assigned by the extension: it must already satisfy the original raw gate conjunction.
- The semantic extension installs only exact original transported values, preserving all other coordinates. At one shared valuation, conjunction of the literal normalized gates plus agreement away from the hidden names is equivalent to the original raw conjunction and equality with the canonical extension; hence it exists uniquely exactly when the original conjunction holds.
- This is not an evaluator that discovers original outputs, a topological sorter or circuit parser, a mixed general DAG theorem, a code/effectivity extension, or a decision-procedure theorem.
