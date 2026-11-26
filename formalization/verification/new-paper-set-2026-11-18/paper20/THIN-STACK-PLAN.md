# Isolated current-paper rational Cartier stack

Decision: no legacy import edits. Prior L0 target/candidate edition remains blocked and is copied byte-for-byte with provenance into `blocked-legacy-import-edition/`. New declarations will live in the distinct namespace `LogicLineages.CartierObserverCurrent.Thin`, with new `Thin*` files. Original targets and frozen pins remain untouched, not silently overwritten.

## Literal definitions and minimal direct imports

1. `ThinPolynomialDefinitions`: import `Mathlib.Algebra.Polynomial.Degree.Operations` and `Mathlib.FieldTheory.Perfect`. Define the finite polynomial selector exactly as sum over range(P.natDegree+1) of monomial n (P.coeff (Nat.bit b n)). Define sqrt digit by mapping this polynomial with inverse Frobenius. These are the original literal formulas under new names; no PowerSeries or legacy LogicLineages imports.
2. `ThinRationalDefinitions`: import the new polynomial definitions and `Mathlib.FieldTheory.RatFunc.AsPolynomial`. Define canonical rational sqrt digit as E(sqrtDigit b (f.num*f.denom))/E(f.denom); define C as its true digit and L0 as C(X*f). Use actual RatFunc and its canonical numerator/denominator, including zero. AsPolynomial is necessary for genuine X/C, not a replacement state model.
3. `ThinTargets`: import new rational definitions only. Freeze full polynomial coefficient/square decomposition, actual rational decomposition/uniqueness/characterization, C square pullout/additivity, local integer-power rules, L0 identity and L0 local rules. The final two targets retain exactly the already reviewed mathematical statements, expressed using the fresh literal operations. Do not assume decomposition or uniqueness as hypotheses.

## Proof closure

4. `ThinPolynomialProof`: prove exact coefficient selector directly by finite-sum coefficient calculation; prove sqrt digit coefficient and polynomial square decomposition with `Mathlib.Algebra.Polynomial.Expand` and minimal arithmetic tactic import if needed. Adapt only the pure coefficient part of old PolynomialDigitProof plus CartierPolynomialProof, not its series theorem/imports.
5. `ThinRationalProof`: prove canonical rational square decomposition using num_div_denom; prove uniqueness using genuine RatFunc.intDegree parity (import RatFunc.Degree); characterize C by unique decomposition. Use explicit CharP.Two, FieldSimp, Ring, Omega imports as needed, never umbrella Mathlib/tactic imports.
6. `ThinLocalProof`: derive square pullout, constants killed, integer powers and even-selector local laws from proved decomposition/uniqueness. Use rational arithmetic and the fixed actual sqrt automorphism, not any oracle fields.
7. `ThinStatementChecks`: exact aliases to every frozen public target; named axiom audits in defining proof modules and comparator. Local closure should be these seven files plus existing Audit, with no old ordinal series/rational suppliers. The optional old-operation bridge is unnecessary for source correctness and deferred to avoid restoring the broad import graph.

Original supplier files will be copied with hash provenance for each adapted proof/definition. Every new public claim must pass independent source correspondence review and the unchanged native checker; previous proofs are templates, not inherited checked objects for these new definitions.

## Cap feasibility, not a guarantee

This removes the gratuitous PowerSeries.Inverse/series continuation/observability branches from BOTH definitions and proofs. It does not remove Perfect (which imports KummerPolynomial and Separable), actual RatFunc.AsPolynomial/degree (valuation machinery), or essential proof tactics. The earlier limit was reached at CartierLocalTargets with about1.38GB file-backed plus193MB anonymous RSS. Avoiding series and its suppliers plausibly helps but static import counts/olean sizes cannot certify resident memory. Neither declaration splitting alone nor a passed definition gate proves the full proof gate will fit.

Measure only through ordinary `scripts/check.py` under the unchanged2048MiB heap/1536MiB RSS/2048MiB free/180s wall/90s CPU/single-thread profile and exclusive parent queue. First run the new exact target/statement closure when authorized, record all failures, and stop at another resource failure rather than raise caps or rerun unchanged. New source hashes and reviewed new comparator make this a genuinely changed input, not a retry of the blocked edition. No external direct Lean experiment or resource weakening is proposed.

This remains a supporting-only L0 packet. Even successful completion does not establish mixed properness/transient, profile bijection/descent, output, or arbitrary continuation observer.
