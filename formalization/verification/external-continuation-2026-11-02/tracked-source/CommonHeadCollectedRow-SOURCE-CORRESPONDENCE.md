# Common-head equal-input collection

Source: paper08, `thm:common`, proof lines855–874.

The executable `collect` enumerates the actual input keys of the finite signed row, deduplicates them, sums all signed coefficients at each equal key, and removes precisely zero blocks. The first target preserves the weighted sum for every evaluator, hence for the actual common-head evaluator. The second target supplies distinct remaining inputs, nonzero coefficients, literal block coefficients, original-key witnesses, and nonincreasing absolute coefficient mass.

The actual target applies the preceding actual large-row theorem at the original printed threshold `max(4,2C,4|K|+4)`. Every surviving key inherits the original genuine-input and threshold bound. All-canceled rows have value exactly K. A nonempty collected row has an attained greatest surviving input, and every such greatest block determines the sign; a larger canceled block has no role. No input distinctness or nonzero assumption is imposed on the original row.

This is a pointwise literal collection and large-branch supplier, not finite total-preorder formula enumeration, small-input recursion, nested layer compilation, or decidability. It makes no claim about the separately restricted signed kernel recursion.
