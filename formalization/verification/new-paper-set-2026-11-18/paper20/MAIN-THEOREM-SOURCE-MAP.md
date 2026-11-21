# Current20 `thm:main`: source map of the frozen target

Target: `LogicLineages.CartierObserverCurrent.MainTheorem.Targets.CompleteMain`
(`MainTheoremTargets.lean`, `MainTheoremBoundaryTargets.lean`). Frozen before proof in
`MAIN-THEOREM-FREEZE.json`. Written by the local Claude root on 21 November 2026. **No independent
pre-scope review was run**; this map is the author's own correspondence argument.

## Why a conjunction

`thm:main` (paper.tex 85–112) opens with "The constructions below have the following properties" and
prints four items. The closing section of the paper (paper.tex, "Consequences and the remaining scalar
question") names the numbered statements that prove each item: `thm:transfer` for the count transfer;
`thm:observer`, `thm:residue-observer` and `lem:observable` for the two observer representations; "the
explicit boundary calculation and `thm:actual-period`" for the linked-input period claim. Each of those
statements already has an accepted frozen comparator. The target is their conjunction, item by item, plus
two clauses that make a printed specialisation literal.

## Item by item

| Printed item | Formal clause | Supplying accepted record |
|---|---|---|
| 1. Complete deletion of one ω^d suffix, retained mass c ≥ 0, initial total norm ≥ c+d+1, every budget ≥ current norm and ≡ S ≥ c mod Q_d = d!·m^(d−1): count ≡ p_d(S−c) mod m | `CountTransfer` = `FullBudgetTransfer.Targets.CompleteTransfer` (numerical form and actual retained-prefix form; `restrictedPartitionPeriod d m = d! * m^(d-1)`) | 192 `thm:transfer` |
| 2a. Binary coefficients of ∏(1+z^i)^(-1) computed exactly by two explicit linear maps on a space of dimension d(d+1)/2 over F2 | `CompleteStateUpdate` (degree D, both matrices and their entries) and `CompleteSelectedCoefficient` (`p_d(n) mod 2` as the e0-coordinate of the ordered matrix product) | 151 `lem:matrix`, 157 `thm:observer` |
| 2b. Distinct numerator states have distinguishing continuations of length ≤ ⌈log2(d(d+1)/2)⌉ | `CompleteObservability` (general A with A(0)=1, deg A ≤ D) and `ActualSourceBinaryObservability` (the same at the actual A_d and D = d(d+1)/2, d > 0) | 161 `lem:observable`; the source clause is the previously proved `OrdinalComparison.actualSourceBinaryObservability` |
| 3. After an explicit finite transient the complete residue profile is closed under both selectors; updates b ↦ b^(1/2) and b ↦ (ζb)^(1/2); scalar output Σ b_ζ/ζ | `BinaryTransient` and `CompleteResidueObserver` (bijection, finiteness, both transitions, output, every continuation) | 048 `lem:binary-transient`, 095 `thm:residue-observer` |
| 4a. For every v ≥ 4 the descent from ω^(ω+1)+(v−4) has an explicit first ω^ω-block parity | `CompleteEntry`, `CompleteOmegaBlock`, `ActualBoundaryParity` (equation (δ)), and the new `LinkedFirstBlock` | 208 `lem:entry`, 203 `prop:omega-block`, 210 (supporting) |
| 4b. On its linked parameters a primitive-root residue tuple has exact period 2(log2 B − 1), B = G(G(v)); every eventual period of the complete differential Cartier state is divisible by it | `ActualPeriod.Targets.CompleteActualPeriod` (`u = Phi v`, `B = Phi u`, `r = Nat.log 2 B - 1`) | 699 `thm:actual-period` |

## The one new statement

`LinkedFirstBlock` glues `lem:entry`, `prop:omega-block` and equation (δ) on the actual family. For every
v ≥ 4, with a = ω^(ω+1)+(v−4), u = Phi v, q = (u−1)/3, p = ω^ω·(q−1), e = u−4, d = Phi u − u + 3 and
H = `actualOmegaCopyCount e u`:

- `actualOrdinalNorm a = v` and `actualOrdinalNorm p = e`;
- the actual descent step of a is p followed by the head block of total norm u above ω^ω;
- for every i ≤ H the state after i further actual steps under the unchanged control `Phi` is p plus the
  i-th state of the numerical copy deletion; at H it is p plus a finite ordinal; before H it is at least
  p + ω;
- H mod 2 = (1 + p_d(Phi(u+1) − e)) mod 2.

It says nothing about the later copies of the same Θ segment, about the scalar coefficient, or about a
larger typed-source realisation, matching the caveats printed after the theorem.

## What the target does not contain

`lem:local`, `lem:poles`, `cor:scalar-profile`, `lem:residue`, `lem:bounds`, the descent-section
statements and `thm:envelope` are accepted separately and are not conjuncts here: `thm:main` does not print
them. The orbit clause of item 4 is over the algebraic closure of F2, as recorded in 699.
