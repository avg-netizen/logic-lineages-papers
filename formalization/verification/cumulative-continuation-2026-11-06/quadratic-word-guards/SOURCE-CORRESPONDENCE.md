# Quadratic V/V word guards: exact source correspondence

Baseline: `036b3ae323e98e0090939071d1d0043683ec0e4b`. The only new mathematical files belong to `QuadraticWordGuardCompletion`. Every previously tracked file is preserved.

## Source statements

- Paper08, lines 288–300: equation V is the literal `rawQuadraticShift j t = Phi^[((Phi t / 2 : Nat) : Int) + j + 1 |>.toNat] t`. Positive signed depths are conclusions of the comparator, not assumptions hidden by totalization.
- Lines 357–366: the degree-two uniform estimate compares adjacent actual inputs with an arbitrary additional iteration allowance. The proof uses the existing exact `QuadraticSeparation.Proof.uniformQuadraticSeparation` with allowance one; it does not replace that supplier by a weaker oracle or re-prove the full rank-d theorem.
- Lines 559–572: arbitrary interior words are evaluated at the original raw inputs. The actual common cutoff pulls the scalar threshold through both structural `reachTail` maps, paying all dynamically reached original domains.
- Lines 584–602: outer fixed shifts cannot close a diverging unequal-core gap. Quadratic heads compare by actual input, then signed depth index; outer shifts decide only when both match. Equality retains all three exact conditions.
- Lines 614–638: deleting the two outer rank-two heads is consistent with the proposed range recursion. This component does not formalize the full decreasing ordinal measure or complete recursive guard construction.

## Frozen target map

1. `QuantitativeQuadraticGap` proves positive depths and actual input lower bounds, then an arbitrary additive gap K for the input/index strict order, at the explicit cutoff `|j| + |k| + K + 8`.
2. `ShiftedQuadraticOrder` proves positive shifted integer values and exact strict/equality/weak comparison. It retains arbitrary signed outer shifts and uses them only in an exact input/index tie.
3. `QuadraticWordGuardCorrect` lifts the scalar result to any admitted original interior words A and B. It proves both complete source domains and reduces to the actual `wordValue A x` and `wordValue B y`, without fresh independent values, inverse counters, or altered schedules.
4. `GuardPrograms` proves the literal scalar and word cutoff programs primitive recursive in both word codes, both depth indices and both outer shifts.

## Scope and source schedules

V is directly the source quadratic function; this component introduces no companion schedule. General interior-domain suppliers retain their proved original-source bridges and explicit `c+d+1` thresholds. No use is made of a companion X or E as though it were definitionally the original source process.

The checked counter/counter, counter/Phi/V/X, coherent factorization and equal-rank X suppliers remain preserved. Remaining work includes shifted ordinary Phi/X comparisons, mixed-rank source expansion, counter/leaf and nonlinear/leaf growth, global guard recursion and termination, same-variable final decision, ranked row cancellation and existential decision. No numbered source theorem is promoted; the register remains 167 checked, 2 inherited, 20 pending / 189.
