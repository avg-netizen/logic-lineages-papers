# Common-head guard deletion and original-index transport

Source: paper08 `thm:common`, proof lines876–891: remove one occurrence after fixing its entire argument, translate guards without changing shared variables.

The first target proves exact evaluation and the exact variable list under arbitrary guard-index renaming, including repeated/shared destinations. The deletion map reinserts the removed occurrence position, leaving all surviving original labels in order; the second target identifies the entire signed input row after deletion and proves every surviving index remains in the original range and is different from the removed index.

A small-branch guard expresses input_i=c using only the existing natural constant bounds. The reindexed child guard has exactly the shorter-row valuation, introduces no original input name, and the actual row value agrees with folding the fixed closed J_lambda(c) into K. The complete argument is fixed before evaluation; no open input or arbitrary basis value is substituted for it.

This is the deletion/substitution bridge for the future recursive row formula. It does not itself construct that recursive compiler, translate preceding-level expressions, establish nested layer formulas, or prove decidability. Small/genuine threshold selection remains in the previously proved small-fold supplier; this algebraic bridge is valid even without that additional domain restriction.
