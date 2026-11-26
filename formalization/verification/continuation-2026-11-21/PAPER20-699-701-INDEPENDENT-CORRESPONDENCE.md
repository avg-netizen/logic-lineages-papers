# Independent printed correspondence: Paper 20 records 699 and 701

Review of owner baseline `762b1c9122ede8c5b752e0be277ff7657f30f099`,
21 November 2026. No manuscript, target, accepted record, or register was
changed; no compiler or native verifier was invoked in this review. The owner
register says **156 checked / 11 pending** and marks both items checked. The
findings below are separate source review, not a new promotion or an
endorsement of the whole register.

## 699: actual residue-tuple period

[Printed theorem](../../../20-controlled-descents-and-cartier-observers/sections/period.tex#L63)
and [accepted record](../new-paper-set-2026-11-18/accepted/699-actual-period.json).

- **Parameters and tuple.** Literal `v ≥ 4`, `u = G(v)`, `B = G(u)`,
  `r = log₂ B − 1`, and `q = 2^r + 1`. `Phi` is exactly the printed
  `F₅(n+100)`. The linked exponent uses `Nat.log` with `B` an exact
  power of two, not a rounded substitute. The index is the subtype of
  **all** primitive q-th roots in the algebraic closure of F₂. Each
  coordinate is coefficient −1 of the genuine initial Laurent expansion
  of the source differential, not an assumed vector or a chosen subfamily.
- **Exact period.** The map is coordinatewise squaring and the result is
  `Function.minimalPeriod = 2*r`, not only a period bound. The proof derives
  `u ≥ 5`, nonempty primitive roots, an upper period, midpoint exclusion,
  and the remaining proper-divisor exclusion. The last uses the actual
  primitive-root count and nonzero polynomial degree bound. No primality of
  q, or individual coordinate degree, is needed or asserted.
- **Full orbit.** The target uses actual rational functions representing
  the differential `(z^(e−1)/A_d(z)) dz`, with literal
  `e = u − 4` and `d = B − u + 3`; the operator is genuine differential Cartier.
  Whole-state coincidence in the algebraic closure implies equality of
  the Laurent residue tuples at the same poles, hence divisibility by
  `2r`. The printed eventual quantifier is explicit and follows from
  the stronger single-coincidence clause. No existence of a cycle, value
  of a complete-state least period or preperiod, or scalar-period property
  is asserted.

The **literal audited orbit type** is `RatFunc (AlgebraicClosure (ZMod 2))`.
This is the ambient field used for the primitive-root argument. The
reading in `RatFunc (ZMod 2)` follows mathematically by mapping any
base-field coincidence through the actual coefficient-extension homomorphism:
`OrdinalComparison/BinaryCartierExtensionProof.lean` proves that it
commutes with the actual Cartier step and maps the literal linked initial
differential to the algebraic-closure one. Neither 699 nor 701 imports that
bridge in its recorded native closure. Thus the base-field reading is a
semantic consequence with an existing checked supplier, not an additional
literal, audited conjunct of either record.

## 701: the four printed main items

[Printed theorem](../../../20-controlled-descents-and-cartier-observers/paper.tex#L85)
and [accepted record](../new-paper-set-2026-11-18/accepted/701-main-theorem-paper20.json).
I read the frozen targets, assembly and first-block proof, not merely the
author's source map.

1. **Transfer.** `CompleteTransfer` covers complete deletion of
   `omega^d + n` to the first finite suffix. Its retained numerical
   mass is arbitrary `c ≥ 0`, initially at least `c+d+1` because this
   is the actual suffix norm. The entire original schedule satisfies the
   explicit lower bound and congruence `Q_d = d!·m^(d−1)`, with `S ≥ c`,
   `d,m ≥ 1`; the result is `p_d(S−c)` modulo `m`. The actual-prefix
   clause additionally supplies the retained CNF prefix, exact trace and
   stopping point rather than assuming an arbitrary prefix is compatible.
2. **Binary observer.** Literal `A_d`, triangular dimension, both
   explicit F₂ matrices with zero for negative coefficient indices, and
   the ordered least-significant-first product on the actual `e₀` with
   its constant coordinate output match the printed construction.
   Observability specializes to the actual denominator and the
   ceiling-log bound with an actual distinguishing word. The
   coefficient theorem uses `d > 0`, the standing cutoff convention of
   `sections/partitions.tex` line 3 and the domain on which `e₀` exists.
   The zero-dimensional polynomial state case is vacuous for separation;
   the nonzero constant coefficient at `d = 0` is not asserted to be
   represented by a zero-dimensional `e₀` observer.
3. **Residue observer.** The explicit transient is
   `Nat.clog 2 (sum 2^(ν₂ i))` over every factor `1 ≤ i ≤ d`.
   All mixed binary words of sufficient length lead to proper simple-pole
   states, no new poles. The actual F₂ rational-state/profile bijection,
   compatibility, finiteness, both stated inverse-Frobenius updates
   at the actual poles, literal sum `Σ b_zeta / zeta` with F₂ output,
   and every remaining source continuation are present. This is not an
   executable splitting-field factorization claim.
4. **Linked first block and period.** The new `LinkedFirstBlock` applies
   the accepted entry calculation and the actual retained-prefix deletion
   trace to `Theta + (v-4)` for every `v ≥ 4`, with
   `Theta = omega^(omega+1)` and the unchanged `Phi`. After the excluded
   initial Theta replacement, the first Omega copy retains precisely
   `Omega *((u-1)/3-1)` of norm `e = u − 4`. The trace remains above the
   finite-tail boundary before `H`, first reaches the retained prefix
   plus a finite tail at `H`, and records
   `H mod 2 = (1+p_d(C−e)) mod 2`, `d = B − u + 3`,
   `C = G(u+1)`, the modular surrogate rather than next operating budget
   `G(B)`. The conjunction includes 699 on literally those linked
   parameters, with the ambient-field caveat above. It claims neither
   a later-copy count, typed-source realization, nor scalar nonperiodicity.

No missing printed mathematical clause was found on these source domains.
This review does not claim a full-root build or a finite-field algorithm
absent from the exact target.

## Read-only evidence and chronology

- Both saved receipt/evidence inventories match all live module source
  hashes (699: **79**; 701: **324**), recorded zero module errors, and the
  fixed Mathlib profile 2048 heap / 1536 RSS / 2048 minimum free / 90 CPU /
  180 wall / one thread. The whole checked aliases use only
  `propext, Classical.choice, Quot.sound`; 41 and 185 recorded named
  declarations respectively are standard-only. The accepted evidence
  SHA-256 values match their archived payloads. 699's 14 original frozen,
  8 split frozen, and 19 final-review pins match; 701's 17 frozen and 27 final
  pins match. This checks source/receipt/evidence consistency, not a fresh
  replay of the originating host's compiler or object files.
- 701's `MAIN-THEOREM-FREEZE.json` metadata says 04:40:00Z, later than its
  recorded acceptance 04:03:56Z. The archived target-only wrapper shows PASS
  at receipt `1795233386424810386-2713525` (03:56:26Z); both Main and Boundary
  target entries in the final 324-module evidence carry that earlier
  receipt and the same frozen source hashes. Full proof receipt
  `1795233656007135223-2714432` is 04:00:56Z. The preserved receipt order
  supports earlier identical target bytes; the handwritten timestamp is
  inconsistent as written and is not used to establish chronology.
  Preserve the original file and record the discrepancy additively.

## Additive base-field comparator assessment (not staged)

The narrow missing literal base-field interface would have two clauses:
for `v ≥ 4`, every coincidence of complete Cartier states, and
respectively every eventual period of that same state, has shift divisible
by `2*(Nat.log 2 (Phi (Phi v)) - 1)`. The initial coefficient is exactly
`actualBinaryRationalDifferential (actualLinkedCutoff (Phi v))
  (Polynomial.X ^ (actualLinkedOffset (Phi v) - 1) : Polynomial (ZMod 2))`.
Both state equalities are in `RatFunc (ZMod 2)`, not in a projection, a
quotient by equality of residues, or a rebuilt control. Assert neither
existence of a period nor its value or anything about scalar outputs.

The needed proof is a one-way transport: use the **existing** literal
coefficient extension, its Cartier-step commutation, an induction on
actual iterate count, and its equality on the actual initial expression.
Apply the homomorphism to a given base-field state coincidence and use
699's stronger coincidence clause. The eventual clause then takes
the actual first comparison in the eventual range. Injectivity is not
needed for this one direction; no orbit or periods are chosen.

A target-only module would directly import `BinaryPoleRemovalDefinitions`,
`CartierRationalDefinitions`, and `LinkedResidueDefinitions` (19 existing
project modules by static import scan), not the large 701 assembly. A
small proof may use private imports of `BinaryCartierExtensionProof`
and `ActualPeriodStatementChecks`; their combined planned dependency
closure is 90 existing project modules by the same scan. The legacy
external component `BinaryCartierExtensionStatementChecks.json` pins all
four unchanged current extension source files and records standard-only
audits from 30 October, **under the older larger profile**. It does not
supply native evidence for the new wrapper at the current caps. Freeze
this separate source-exact proposition first, perform the target-only
preflight, then gate the new proof and actual closure under the fixed
current Mathlib profile. Preserve and report any resource stop rather
than load 701, modify legacy code or enlarge caps. No target, Lean
proof, or native gate was staged during this assessment.
