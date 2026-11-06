# Bounded terminal nonlinear-word growth

Source: paper08, `08-multivariate-collapse-comparison/paper.tex`, lines 627–636 (`lem:guards` proof). The source requires every nonlinear word at x to exceed a shifted leaf at y ≤ x on a computed tail, including the same-variable case. This component proves a literal exponential lower bound and this terminal comparison, not a full guard compiler.

`Nonlinear` means an actual non-shift letter in the original word. All admitted Phi, V, X and E letters are covered, including unused fields and arbitrary signed indices. `LetterGrowth` retains the exact original letter domain. For E the proof must invoke `SourceProcessBridge` at the explicit stronger threshold c+d+1, then the genuine quadratic count and finite-degree lower-count supplier; original and companion schedules are never identified outside that bridge. For V/X positive signed iterate depth is paid by the existing letter tail.

Let W be the sum of absolute signed indices. `CompensatedGrowth` has 2^(t-W) ≤ value+W at the existing word tail. `growthOffset=W+1` and `growthTail=wordTail+2W+2` absorb that loss, yielding the source's 2^(t-M) lower bound at the actual successive arguments. `terminalTail=max(growthTail,2M+abs(b)+2)` pays the fixed opposite shift and gives shiftedLeaf(y)<word(x) whenever both raw inputs reach the tail and y≤x. No new variables or substituted raw arguments are introduced.

Full recursive guard construction, ordinal termination, all-shift normalization, the general same-variable decision procedure, ranked row cancellation and full first-order BASE remain pending. The global source register is unchanged (167 checked, 2 inherited, 20 pending / 189).
