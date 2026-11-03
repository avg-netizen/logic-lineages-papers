# Common-head finite large-input guards

Source: paper08 `thm:common`, proof lines855–874, finite guarded equal-input partitions.

The syntax contains only truth, falsity, equality and strict order between original labeled inputs, a natural constant lower bound, and finite Boolean operations. It contains no head-evaluation atom or independent basis value. Boolean masks enumerate every possible equality block at a labeled input; each mask sums the literal fixed signed coefficients. Its exact guard forces both equal and unequal entries, so inconsistent masks contribute no valuation.

The large-branch formula retains the original printed threshold. It asserts either all blocks cancel and the signed constant has the requested sign, or a block has the requested nonzero sign and every strictly larger input has zero block coefficient. This finite equality-mask enumeration is an equivalent guarded-partition implementation, not an assumption of arbitrary coherent relations. The actual valuation interprets every equality/order atom, and the established collection and surviving-maximum theorems prove the result. Arbitrary duplicate input values, zero original coefficients, empty rows, and arbitrary integer requested signs are covered. Only original labeled input names occur.

This component constructs the exact large-branch finite guards, not the recursive small-branch formula or lower-layer substitution. It does not yet claim the full nested common-head theorem or decidability. Guard syntax is a direct finite fragment of the printed arithmetic language; substitution of preceding-level expressions is a later obligation.
