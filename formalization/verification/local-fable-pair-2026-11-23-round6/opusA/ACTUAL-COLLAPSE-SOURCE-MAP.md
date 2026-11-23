# ACTUAL-COLLAPSE: source map (Opus A, round 6)

This instantiates the abstract `CollapseData` / `TowerHypotheses` of #1463 with actual definitions, following
ordinals.tex 593–610. **Result: `TowerHypotheses` holds outright for the paper's actual data, with no residual
hypothesis.** The first equality of `lem:tower-cofinality`, `sup_n ψ_B(a_n) = ψ_B(Λ)`, follows for the actual data.

## Modules (`LogicLineages/NativeModule/PersistentMarking/`)

| Layer | Module | sha256 | Receipt |
|---|---|---|---|
| definitions (frozen) | `ActualCollapseDefinitions` | `7af5095634a9f42a13d259d5596d6b438ef5703dc33a7729501d171c705cf952` | `1795413208611141409-3313464` |
| statements (frozen) | `ActualCollapseTargets` | `6d8f2751557fccfa34d7fafcbad3516ce98d9d2689149611313d2896fdc0dbdb` | `1795413235508917218-3313564` |
| norm | `ActualCollapseNormProof`: `normBound`, `normBelowOmegaOne`, `normCountable` | `3e9f2f546e8c79072a5c18f9c3b98e2e0bf05d54ef72125fa4c9108d84fb7893` | `1795413344474868888-3313926` |
| criticality | `ActualCollapseCriticalProof`: `criticalFacts`, `veblenInflationary` | `364a44ba7f411ffd8afd0aec3a763e87e08d6bca053b21bc75d0e4ff71bfe96b` | `1795413452421064524-3314359` |
| existence and (P) | `ActualCollapseExistenceProof`: `collapse_characterization`, `actualCharacterization` | `e0ddcbb22fa46fd1579ab1a752bed2c8767dda179e185c492a10aabae0aef3de` | `1795413498952400102-3314487` |
| assembly | `ActualCollapseAssemblyProof`: `actualTowerHypotheses`, `actualTowerSupremum` | `67137d9dab5cf59ca2a4d068c6d78d332467d7f406a4329dfaad61a8368b22ba` | `1795413517308973235-3314617` (683 modules, all rc 0) |

- All seven theorems have axioms `[propext, Classical.choice, Quot.sound]`.
- Peak RSS: 966,996 KiB, at `ActualCollapseCriticalProof`.

## Definitions against the printed text

| Printed | Lean | Verdict |
|---|---|---|
| "Let Ω be the first uncountable ordinal, a_0=0, a_{n+1}=Ω^{a_n}, Λ=sup_n a_n" | `ActualOmegaTower.omegaIndex = ω₁`, `argument`, `endpoint` (#1479) | literal |
| "The coefficient norm is recursively the maximum of the countable coefficients in the base-Ω representation and of the norms of its exponents" | `coefficientNorm o` = `foldr max 0` over `CNF ω₁ o` of `max coeff (norm exponent)`. The recursion is well-founded on `o`; an exponent equal to `o` contributes 0. | literal on `o < Λ`, where every exponent is below `o` (`log_lt_self_below`, which uses #1479 `EndpointLeast`). The guard affects only fixed points `Ω^o = o`, i.e. `o ≥ Λ`; at `o = Λ` it gives `|Λ| = 1`. `|Λ|` never occurs in (P), which uses only `η < ξ ≤ Λ`. |
| "In particular \|a_n\| ≤ 1" | `normBound` | proved |
| "an N_B-critical ordinal is an orbit value N_B^α(Γ_0)" | `Critical N Γ θ := ∃ α : CountableOrdinal, (orbit .base N Γ α).val = θ`, with `N = veblenValue fix pow` = `B_1 B_0 Next` and `Γ = baseValue fix pow w` = `N_B(ω)` (#1462), and convention-(I) orbits | literal over the repository's semantic `N_B`. α ranges over countable ordinals, the paper's semantic ι. |
| "the strictly inflationary function N_B" | `veblenInflationary` | proved from the arithmetic/ω equations: `N_B ζ = fix g ζ = g^ω(ζ+1) ≥ ζ+1` |
| "These criticals are closed under countable increasing suprema" | `criticalFacts`, 4th conjunct (lub of a strictly increasing critical sequence is critical) | proved: the orbit is strictly increasing and continuous at limits |
| "every value in the critical base sequence is at least Γ_0 > 1" | `criticalFacts`, 1st conjunct | proved |
| "ψ_B(ξ) [is] the least such critical θ for which η<ξ, \|η\|<θ ⟹ ψ_B(η)<θ (P)"; "This uses the defining clause of this particular collapse" | `collapse`: well-founded recursion, `ψ ξ = sInf {θ \| critical θ ∧ ∀ η<ξ, \|η\|<θ → ψ η < θ}` on `ActualIndex = {ξ \| ξ ≤ Λ}` | (P) **as definition**. By #1484 it is the unique function satisfying (P). |
| indices, values | indices are `ξ ≤ Λ` (ordinals; the hereditary norm terminates below Λ). Values are `Ordinal.{0}`, all proved `< ω₁`. | chosen so that `CollapseData ActualIndex Ordinal.{0}` matches the `Ordinal.{0}` value layer of the interface (`Calibration`, `UpperBound`). The countability bound is a theorem, not a type restriction. |

**Existence (the mathematical content).** Two facts carry it:
- `normCountable`: for countable θ, `{η < Λ : |η| < θ}` is countable. The proof inducts over `a_n`. An ordinal below
  `Ω^{a_n}` is the evaluation of its CNF list, whose entries have exponents in the previous level and coefficients below
  θ, and lists over a countable set are countable.
- Regularity of ω₁ (`Ordinal.iSup_lt_omega_one`), plus unboundedness and sup-closure of the criticals.

Together these give an ω-iteration that reaches a critical clause solution. Fable-2's `CharacterizationExists` (`ConditionalCollapseExistence`)
was not usable: its `Solvable` quantifies over arbitrary `prev`, including uncountable values, and that is false for
countable critical values. I used my own recursion with the invariant "earlier values are critical"
(`collapse_characterization`).

**`TowerHypotheses (veblenData fix pow w)`**, for every solution of the arithmetic/ω equations — every field is proved:
- `characterization` (P), by `actualCharacterization`;
- `increasing`, `below`, `cofinal` (#1479);
- `normBound`;
- `criticalAboveOne` and `criticalSup` (`criticalFacts` with `veblenInflationary`).

**Residual list: empty.**

`actualTowerSupremum`: `(⨆ n, ψ(a n)) = ψ(Λ)` for the actual data, via #1463's `conditionalTowerSupremum`.

## BH: the two readings
The paper says: "The Veblen-hull endpoint ψ_B(ε_{Ω+1}) is the BH of the inductive-norm calibration [Pohlers §§9.4–9.5]."

**Reading (a): BH is defined as `ψ_B(Λ)`, the value just built.**
- `BHIdentification` becomes `rfl`.
- `NormTheorem` (E4) then asserts that ID₁-provable atoms have stage below *this* ordinal. Pohlers proves the bound for
  *his* BH (the ψ-collapse of ε_{Ω+1} in his own notation, or the sup of inductive norms). So E4 at `ψ_B(Λ)` is
  Pohlers's theorem *plus* the identification of the two ordinals. The cited identification moves from E3 into E4.
- E1 must then be Simmons's calibration for this (P)-defined collapse. By #1484, (P) determines ψ given the norm and the
  critical class, so E1 also needs our norm and criticality to coincide with Simmons's.

**Reading (b): BH is Pohlers's ordinal, defined independently.**
- E4 is Pohlers's norm theorem verbatim.
- `BHIdentification` (E3, `ψ_B(Λ) = BH`) is a genuine external identification. That is what the sentence and its
  citation describe.

**Conclusion.** The sentence reads as (b): it identifies two independently defined ordinals and cites Pohlers for it.
Under either reading there is exactly one external fact, "Simmons's Veblen-hull endpoint equals Pohlers's BH". Reading
(a) hides it inside `NormTheorem`; reading (b) keeps it visible as E3. I did not assert it.
