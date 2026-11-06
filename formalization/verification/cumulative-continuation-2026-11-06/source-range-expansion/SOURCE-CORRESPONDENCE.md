# Original-source one-step range expansion

Baseline: `15000f70e770e7ab958e52714156a78e1c81ef85`. Only the new component and its evidence are added; every tracked baseline source, manuscript, target, checker, dependency pin and register remains preserved.

## Literal source map

- Paper08 lines 260–281 distinguish the original source schedule from the padded companion and require the stronger `c+d+1` correspondence condition. The new proof converts parent, unsigned inner entry and lower child separately, using `Focused.sourceProcessBridge` at each actual input.
- Lines 288–300 give the signed block recurrence for rank at least three. The transformation evaluates `X^d_(c+d,0)` first and then the lower-rank signed outer head. The output is still total norm; it does not subtract c again.
- At parent rank three, the exposed child is exactly `V_(j-ceil(c/2))`, represented by a quadratic letter with integer index `j-Int.ofNat((c+1)/2)`. It is never represented by the forbidden degree-two X letter. The proof derives the exact quadratic-shift identity from the accepted actual quadratic-count supplier for this branch.
- Lines 559–572 require domains at dynamically reached arguments. The scalar cutoff pays the finite block threshold, the literal original-head tail and the emitted two-letter word tail. The full context cutoff pays the structural reach of that scalar cutoff and the original whole-context domain.
- Lines 603–608 describe expanding a higher-rank head until the appropriate lower rank is exposed. This component proves exactly one such expansion and its contextual validity, not repeated expansion or comparison against another head.
- Lines 614–625 explain why expansion alone may increase written length. The syntax target proves length two and no E nodes; no decreasing measure is claimed here. A later comparison-and-stripping step must justify the complete recursive child's measure.

## Explicit bridge inequalities

For `d=n+3`, the finite block threshold includes `c+2*d+1 <= t` and `c+2*|j|+3 <= t`. Hence:

1. Parent bridge: `c+d+1 <= t`.
2. Unsigned inner bridge: `(c+d)+d+1 <= t`.
3. Its actual companion entry is at least t by iteration domination, so the lower child bridge `c+(d-1)+1 <= entry` also holds.

The accepted unsigned block cocycle remains companion-shaped. Positive parent/child signed depths turn its exact count equation into the signed iterate identity. The separately proved bridges convert each process; original and companion semantics are not identified by convention or an added premise.

## Context and effectiveness

The context target preserves the original A, S and raw x. Equal replacement-prefix values transfer the exact suffix domains and suffix value, including arbitrary negative shifts, without monotonicity or independent witnesses. All literal head/word transformations and both cutoffs are uniformly primitive recursive in their complete raw codes.

## Remaining scope

Repeated mixed-rank exposure, its comparison-and-strip branch, full guard recursion and ordinal termination, terminal growth, same-variable decision, ranked row cancellation and existential decision remain pending. No numbered source theorem is promoted. Register remains 167 checked, 2 inherited, 20 pending / 189.
