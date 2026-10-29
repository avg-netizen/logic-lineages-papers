# External formalization handoff

Local formalization is **paused by the user's request on 29 October 2026**.
All three Codex lanes confirmed stopped; the returned Claude proposal is saved,
and its author process has ended. No local worker should restart automatically.
The user's separately authorized external agent may continue the mathematical
work; it does not need our private Claude automation or session.

## Publication state

The repository version containing this handoff includes the `formalization/`
tree and manuscripts 11–15 together. Use the current `main` branch of
[the papers repository](https://github.com/avg-netizen/logic-lineages-papers).
The earlier commit `fa6bf2a81fe83c1a7e2158a61957cef8dd84cf70` predates these
additions. The user authorized their publication after pausing the local
workers; publication does not restart those workers.

## Required sources and build dependencies

All current mathematical Lean source dependencies are in this repository or
the pinned standard libraries. No accepted or candidate Lean file imports a
private-vault namespace. The calculator dependency is included at
`04-pure-r1-calculator/lean`; the selected modern norm-source closure and its
provenance are also included under `OrdinalComparison/Vendor/R1`.

Install Lean `v4.32.0-rc1` and fetch Mathlib at
`360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56` using the committed Lake manifest.
The development machine borrowed a matching dependency cache; that cache is
not an additional source dependency to obtain from the vault.

Read [README.md](README.md), [AGENTS.md](AGENTS.md),
[TARGETS.json](TARGETS.json) and [MANUSCRIPT-SNAPSHOT.json](MANUSCRIPT-SNAPSHOT.json).
The target register contains 178 numbered manuscript statements and additional
algorithmic/cited-supplier obligations. Six numbered statements are newly
checked, two have the calculator's pre-existing coverage, and 170 remain pending.
Additional components compile without completing their parent statements.
None of the other fourteen papers is fully formalized end to end.

The root `LogicLineages.lean` selects accepted gates. For separate fresh gate
checks, from `formalization/`:

```sh
mapfile -t gates < <(python3 scripts/accepted_gates.py)
python3 scripts/check.py --fresh "${gates[@]}"
```

The [component CI workflow](../.github/workflows/paper-components-lean.yml)
checks the accepted gates. Consult its run for the exact publication commit;
this handoff does not assert that an unobserved CI run has passed.
Local resource limits protect a host with exhausted swap and little available
RAM. Missing headroom and page-I/O timeouts are not theorem diagnostics.
An external machine may use appropriate bounded resources; preserve the exact
mathematical statements and all proof/axiom checks.

## Exact continuation state

- **Papers 02, 12, 14:** start with
  [the stream handoff](LogicLineages/ComputabilityKnowledge/PAUSED-HANDOFF.md).
  `MultiplicationGadgetProof.lean` is an unchanged 200-line Claude proposal for
  the full seven-equation lemma, including its literal syntax and depth bound.
  It has not had its first actual elaboration: the memory guard refused the
  attempted launch. Compile it before a proof-body review, repair actual
  diagnostics, then check the frozen gate and axioms. R001–02 and five source
  foundations passed; reproduction/repair facts are copied into
  `ComputabilityKnowledge/handoff-provenance/`. Private Claude logs are unnecessary.
- **Papers 04–10:** [ordinal status](status/ordinal-comparison.md) and its
  `ACCEPTED-COMPONENTS.json` pin 15 accepted gates. Only `lem:phi-growth` is a
  complete numbered statement in this stream. The repaired ordinal-representation
  completeness proof awaits recheck; its target, calibration and soundness
  compiled. Natural sum/product candidates and their actual-ordinal denotation
  gates remain uncompiled. Normal-notation collapse/predecessor facts must still
  be transported to the full source domains and optimized algorithms.
- **Papers 01, 03, 15:** [models/algebra status](status/models-algebra.md) pins
  nine accepted gates. The first displayed conclusion of the quotient-filtration
  lemma is complete; actual Ulm quotient actions/maps, local bijectivity and the
  full two-conclusion lemma are written but uncompiled. Differential constants
  candidates reached import/time limits without a theorem diagnostic. Forest
  width/leaf facts are checked; Carter's decision supplier and full JEP result
  remain pending.
- **Papers 11, 13:** [main status](status/ultrafilters-rl.md) and
  `LogicLineages/ACCEPTED-MAIN-COMPONENTS.json` pin four complete source statements:
  the finite RL composition counterexample, additive-coordinate dichotomy,
  persistent discontinuity obstruction and Hamel support-length escape.
  The two explicit witness branches, their universal combination and the actual
  `Filter.Germ` quotient-domain properness theorem are written but unaccepted.
  `CoordinateBranch` last stopped in page-I/O after 2.46 CPU seconds, without
  proof diagnostics; its deprecated import has since been replaced by the
  canonical module. `HamelBranchChecks`, `UniversalWitnessChecks` and
  `UltrapowerChecks` have not been reached. The RL policy classification and
  derivative-domain field/derivation laws remain pending.

Every full source target must keep all dependencies between standard libraries
and its conclusion. MRDP, Scott/back-and-forth classification, Löb/coding,
ordinal analysis and other missing suppliers are work to prove, not new premises
which may be added to make a target compile.

## Useful material outside this repository

These are additional reading/reuse sources, **not hidden imports of the current
proofs**. No full-vault access is needed.

1. **The private research repository's reference library:**
   [text catalog](https://github.com/avg-netizen/logic-lineages/blob/main/references/TEXT-CATALOG.md)
   and [source-access guide](https://github.com/avg-netizen/logic-lineages/blob/main/references/PRO-SOURCE-ACCESS.md).
   The catalog indexes 525 extraction/OCR files, about 56 MB, rather than 525
   distinct works or reconstructed TeX. This is useful for the original source
   questions and the cited suppliers missing from Mathlib. Check ambiguous
   formulas against the originals. The manuscript bibliographies also provide
   ordinary source references; these texts are a convenience, not a replacement
   mathematical assumption or a required private build dependency.
2. **The public 3.1.3 Lean development:**
   [alexander-dissertation-lean](https://github.com/avg-netizen/alexander-open-problems-results/tree/main/alexander-dissertation-lean).
   Generic syntax, Hilbert calculus, proof checking and universal-program
   coding may save work. The included
   `ComputabilityKnowledge/handoff-provenance/outside-lean-inventory.json`
   gives selected complete local import closures and observed hashes. No current
   new proof imports those modules. Port only a matching complete closure and
   prove its correspondence to the target theory. The old Wilken hull/minimum
   `FiniteCollapse` is different from this collection's norm-controlled collapse;
   ordinary ordinal addition is different from natural/Hessenberg addition.

The three stream statuses give more specific source locations. All substantive
current manuscripts, fixed targets, candidate proofs and continuation facts
needed to work on them are already in this local papers checkout.
