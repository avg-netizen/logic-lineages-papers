# Independent final review: complete actual period

Approved for full current `thm:actual-period`. Verdict PASS WITH NOTES; nothing blocks marking the statement
checked. Reviewer: a fresh-context Claude subagent on the local host, read-only, no compiler, no Git writes.
It is the same model family as the author of today's proof edits; the pre-scope review of 18 November was by
a different reviewer. Compilation and axiom lines were taken from the native gate and the recursive evidence
file, not re-run by the reviewer.

Statement. All 14 pins of `ACTUAL-PERIOD-FROZEN-PINS.json` and all 8 of `PERIOD-TUPLE-SPLIT-FROZEN-PINS.json`
match the files on disk, including `ActualPeriodTargets.lean` and `period.tex`. The three conjuncts say the
printed theorem at v ≥ 4, u = Phi v, B = Phi u, r = log2 B − 1: the tuple runs over all primitive q-th roots
(q = 2^r + 1) in `AlgebraicClosure (ZMod 2)`, its entries are coefficient −1 of the actual initial Laurent
expansion, Frobenius is the coordinatewise square, and the orbit is that of the actual rational differential
X^(e−1)/A_d under the actual Cartier operator. B is proved an exact power of two, so `Nat.log` has no floor
effect. The simple-pole reading of the tuple entries is paid by the checked initial-residue bridge.

Chain. `fixed_completeActualPeriod` is a plain triple. `halfExponentPrinted` is three definitional
unfoldings (no axioms). `actualExact` applies the dynamics lemma with the upper period, the midpoint
exclusion and the small-exponent exclusion; each is a closed theorem for u ≥ 5 with no premise passed in.
The four legacy suppliers (`actualResidueFrobeniusUpperPeriod`, `actualResidueFrobeniusMidpointNonfixed`,
`actualResidueSmallExponentNonfixed`, `actualLinkedResidueArithmetic`) are theorems over an arbitrary field
with an F2-algebra structure. `statePeriodic` has only u ≥ 5 and the state equality as hypotheses and uses
the iterated-residue law (no regularity premise) and the initial-residue law. The simple-zero and
nonvanishing-derivative facts are derived, not assumed.

Exactness. With minimal period s and s·k = 2r: k = 1 is the claim, k = 2 is excluded by the midpoint, k ≥ 3
gives 3s ≤ 2r and is excluded by the small-exponent case. One non-fixed coordinate suffices for a tuple, and
non-emptiness of the index set is proved (`rootExists`).

New lemma. `primitiveRootOfNeZero` (separable, split X^q − 1; cyclic group of order q) is correct; universe 0
suffices for its only use. `actualModulusOdd` feeds it soundly.

Private imports. The full local import closure (78 modules plus the second gate) was walked through private
and public imports; every `source_sha256` in the evidence equals the file on disk; no forbidden token; no
definition, target, legacy or checker file modified; the cap default is unchanged. The pinned toolchain's
axiom collection reads per-declaration axiom sets computed with bodies, so a privately imported supplier
cannot drop out of the audit.

## Limits to carry with the acceptance

- Tuple statement only: nothing about the degree of an individual residue, about F_{2^{2r}}, or about the
  order of two modulo q.
- Orbit: divisibility only. No existence of an eventual period, no value of period or preperiod.
- No scalar output: nothing about the selected coefficient, δ₄(v) nonperiodicity, traces or observers.
- Not paper 20 `thm:main`, whose fourth clause needs its own target; not a re-acceptance of `lem:residue`,
  `lem:bounds` or `lem:local`.
- The orbit lives in `RatFunc (AlgebraicClosure (ZMod 2))`. Reading it over F2(z) needs Cartier-equivariance
  of the base change, which is not in this packet.
- That `actualDifferentialCartier` is the paper's C rests on the decomposition in this closure plus the
  uniqueness of a² + X b² from the separately accepted Basic packet.
- Domain u = Phi v, v ≥ 4 only. Focused closure only; no full-root or CI build.
