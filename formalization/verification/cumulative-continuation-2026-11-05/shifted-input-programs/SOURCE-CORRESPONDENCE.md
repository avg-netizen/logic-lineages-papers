# Actual numeric shifted-input guard compiler

The typed guard lowering is mirrored by an explicit total numeric stack
compiler. Atomic signed-input comparisons use literal encoded linear rows.
Existing postfix equality-mask and maximal-block programs are lowered to the
unchanged NormalForm radix-six syntax. Out-of-range indices and malformed
postfix stacks have fixed defaults; exact calibration is required only for
literal source encodings.

Original row-data extraction keeps every Phi occurrence, including repeated
names and zero coefficients, in order. Targets require exact code equality for
the cancellation, block-coefficient and active-sign formulas, and genuine
primitive recursiveness of all these specified programs. This does not claim
effectivity of inactive deletion masks, the full maximal-name transformer,
hyperPhi cases or the global nonlinear decision procedure.
