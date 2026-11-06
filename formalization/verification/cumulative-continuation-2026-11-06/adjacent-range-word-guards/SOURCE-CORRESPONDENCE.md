# Adjacent mixed-rank comparison and immediate stripping

Baseline: `229c65886a069d7f0fa45813d942d6a8f02fbaf9`. All previously tracked sources, manuscripts, targets, checker/dependency files and the global register remain unchanged.

## Source comparison cases

- Paper08 lines 275–300 and 603–608: first expand only the higher head, retaining its unsigned higher-rank occurrence with mass c+d at the original argument. Immediately compare its exposed lower-rank outer head against the opposite head of that rank.
- `AdjacentKernelGuard` implements ranks n+4 versus n+3. The left retained word is exactly `A ++ [X^(n+4)_(c+n+4,0)]`. It is evaluated at original x, not a fresh variable. The exposed rank-n+3 comparison uses the accepted shifted equal-rank source guard, including reverse mass, signed depth and exact outer-shift ties.
- `CubicQuadraticGuard` handles rank three against V. The exposed index is exactly `j-ceil(c/2)`; the opposite quadratic index k remains arbitrary. The accepted shifted V/V guard then compares the actual retained left word against B(y), including the exact adjusted-index tie.
- Lines 559–572 and 584–602: arbitrary admitted interiors, signed depths and signed outer shifts remain literal. Each cutoff pays the exact source expansion context and the relevant complete same-rank guard. Both original word domains and the generated retained-word admission/domain are conclusions.

## Exact local decrease

The source measure at lines 614–625 applies after comparison and stripping, not after expansion alone. `AdjacentHeadDecrease` proves a full local count identity at every range rank: the transformed pair has exactly one fewer occurrence at the opposite lower rank, and the same count at every other rank, including the retained higher rank. E count is unchanged. Both original interiors occur once.

The count target uses the generic genuine `lowerHead`. At n=0 it is quadratic; choosing retained mass zero yields any literal V index k. At positive n it is the opposite rank-n+2 X head. Non-range letters receive rank zero only in the count definition; the identity remains valid there too.

## Source domains and effectiveness

Original-source calibration is inherited from the unchanged accepted SourceRangeExpansion supplier, with explicit parent, inner and reached-child bridges at genuine thresholds. Exact context equality transfers signed outer suffix domains. No companion schedule substitution, inverse counter or independent interior witness is introduced.

The literal retained-word constructor and both composed cutoffs are uniformly primitive recursive in every word/rank/mass/index/shift code.

## Boundary

Only adjacent rank gaps, including the cubic/quadratic boundary, are handled. Arbitrary-gap exposure and comparison, complete recursive guard construction and termination, terminal growth, same-variable decision, ranked row cancellation and existential decision remain pending. No numbered source theorem is promoted. Register remains 167 checked, 2 inherited, 20 pending / 189.
