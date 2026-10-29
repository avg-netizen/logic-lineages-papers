# Paper 13: concrete semantics and source correspondence

Current coverage, **29 October 2026, 14:54 UTC**: independent exact-type and
standard-foundation audits have accepted gates for all eight numbered
statements of the local manuscript, together with the concrete semantic
suppliers below. Root owns aggregate integration, the global target register,
and fresh whole-project checks. Individual receipts below do not assert a
later whole-project run, remote publication, or remote CI success.

The original abstract `Definitions.lean`, `Targets.lean`, `Noncomposition.lean`,
and `StatementChecks.lean` remained unchanged throughout this continuation.
Every new semantic/target/gate bundle was independently reviewed, target-compiled,
and hash-frozen **before** its separate candidate proofs were authored. Repairs
changed candidate proofs only, except explicitly reviewed pre-freeze import or
bound-variable syntax corrections. Every accepted gate's axiom closure is
contained in `propext`, `Classical.choice`, and `Quot.sound`.

## Sources and provenance

- `13-reinforcement-learning-transformations/paper.tex`, SHA-256
  `d3b396ff59814360751ad0b602c60a08d6602c7cce4a0459d3686e270ee660d8`.
- `13-reinforcement-learning-transformations/SOURCES.md`, SHA-256
  `71736893d8b5ea6d72252cdc6f9381d9c415727602d624d42e5a4bf128a9cb1c`.
- The full local manuscript was inspected. Its source contract identifies
  Alexander–Pedersen arXiv:2112.07752v5 Definitions 2 and 6–9. No private source
  import, unproved cited supplier, or hidden interaction oracle is needed by
  this proof chain.
- Portable accepted-file hashes and gate metadata belong in the root-maintained
  [`ACCEPTED-MAIN-COMPONENTS.json`](../ACCEPTED-MAIN-COMPONENTS.json) and
  [`TARGETS.json`](../../TARGETS.json). Receipt identifiers below are relative
  to `formalization/build-reports/` when those local reports are present.
  Independent review/freeze records are task-workspace artifacts outside the
  repository; their record names are not presented as repository-relative links.

## Accepted numbered statements

| Source label | Exact gate module | Successful receipt |
| --- | --- | --- |
| `thm:classification` | `ClassificationChecks` | `1793284430421831483-6.json` |
| `lem:affine` | `AffineChecks` | `1793276439508088598-6.json` |
| `prop:positive` | `PositiveTransformationChecks` | `1793279726045089136-7.json` |
| `lem:separator` | `SeparatorChecks` | `1793283759280556470-7.json` |
| `lem:mixture` | `MixtureChecks` | `1793283447388969557-7.json` |
| `prop:negative` | `NegativeTransformationChecks` | `1793284333873120566-6.json` |
| `prop:noncomposition` | original `StatementChecks` | `1793248443025567130-2.json` |
| `prop:cross` | `CrossObstructionChecks`, with the general reward-stream bridge | `1793285539025721274-6.json` |

The cross-order result is separate from the classification. Its acceptance
uses both the general reward-stream bridge and actual environment-mixture
suppliers, not merely an abstract implication or a rescaled DD example.

## Actual policy domains and interaction semantics

`PolicyDefinitions.Alphabet` has finite nonempty action/percept carriers in
`Type`, integer reward, and explicit percepts of reward 0 and 1. There is no
global cardinality-at-least-two assumption on actions. Disjointness is supplied
by `Action ⊕ Percept`, even if the underlying carrier types coincide.

Environment histories are `List (Percept × Action)`; agent histories add one
final percept. Deterministic functions and nonnegative, normalized rational
kernels are defined on **every** such history, including off-path histories.
Independent literal-word grammars define `(PA)*` and `(PA)*P`.
`HistoryCorrespondence` proves that the typed encodings are injective and onto
those grammars, with the correct percept/action counts.

`PositiveTrace n` is `Percept` at zero and
`Percept × Action × PositiveTrace n` at successor. Thus horizon `n+1` has
`n` actions and `n+1` percepts; horizon zero is `Unit`, the empty trace. There
is **no final action** after the last reward. Actual trace weights multiply
environment/percept and policy/action kernel masses. Finite value sums these
weights times the rewards of all recorded percepts, including the initial one.

`TraceCorrespondence`, `FiniteTraceLaw`, `DeterministicCalibration`, and
`InitialHorizonCalibration` prove literal-process correspondence, normalization,
actual deterministic execution, `V_0=0`, and the correct initial expectation.
Their seven-gate semantic bundle passed `1793276786574134652-6.json`.

`Admissible` explicitly requires a finite real limit for every deterministic
policy **and** every stochastic policy, not just image policies. There is no
uniform value bound. Deterministic environments embed as actual point masses.
`value` is chosen from the actual convergence proposition; `ValueLimit` proves
convergence to the selected real and uniqueness. The four `framework S X Y`
adapters use all policies and all admissible environments of the selected
kinds and derive their values from this limit, without modifying the frozen
abstract `Framework`.

## Affine family and positive transformations

`firstActionMixture a0 a1 t` chooses `(1-t) δ_a0 + t δ_a1` exactly when the
completed-round history is empty, independently of the initial percept.
Every later history uses `δ_a0`. The endpoints are actual deterministic
embeddings. This definition works even when `a0=a1`; distinct actions are
required only by the later positive-transformation nontriviality witnesses.

The finite trace and expectation affine laws hold for every raw environment,
without admissibility. Taking real limits proves `lem:affine`, including its
deterministic-environment specialization.

`oneShot test` emits zero initially, rewards the first recorded action at the
second percept iff it passes `test`, then emits zero forever. Its off-path rule
is complete. All-policy finite expectations stabilize at horizon two, yielding
full admissibility and exact values for equality, inequality, false, and true
tests. Five gates passed `1793279546440984576-7.json`.

The positive construction uses these actual environments and the sign of the
two endpoint values. Its agent codomain is genuinely deterministic when
required. Faithfulness and **both** existential nontriviality clauses are
proved for all source/target environment-kind choices. No effectiveness or
injectivity restriction is added to the manuscript's set-theoretic maps.

## Behavioral mixtures and scripted separators

The agent mixture uses action-only likelihood products on recorded histories.
Its posterior rational kernel satisfies the manuscript quotient formula;
zero denominator forces both branch likelihoods to vanish and no extension
can revive them. A common environment-likelihood factor gives the actual
trace mixture identity, then finite expectations and limiting values.
This is not pointwise averaging of policies and uses no hidden random seed.
All nine mixture gates passed `1793283447388969557-7.json`.

The separator proof derives a finite first action divergence from **actual
unequal values**, not mere syntactic disagreement at an unreachable history.
Its deterministic environment emits the entire prescribed percept script
regardless of action deviations, then an exact-action-match indicator reward,
then zero. The offset is the unrestricted signed integer sum of script
rewards; no zero-reward copy of an arbitrary percept is presumed.

A generic actual finite-reward-tail theorem supplies full all-policy
admissibility. Every deterministic policy has exactly one of `C` and `C+1`;
the original two policies are separated. Stochastic interval bounds are
proved separately and do not replace that exact deterministic two-value
range. All ten separator gates passed `1793283759280556470-7.json`.

The negative transformation proof combines the separator with an actual
behavioral midpoint. Faithfulness would force a deterministic target value
strictly between the two allowed values. The singleton-policy theorem proves
both actual policy types subsingleton when actions are subsingleton; its gate
passed `1793284391416110404-6.json`. The final classification includes this
singleton qualification, not just the nontrivial-action table.

## Cross-environment comparison: general source scope

`CrossFaithful` is the literal stronger comparison of possibly different
environments. `NoCrossWithVariation` excludes pairs satisfying this contract
and the **second** nontriviality condition only. It does not silently add the
first nontriviality condition or conflate this contract with same-environment
faithfulness.

`EnvironmentMixtureDefinitions` constructs actual posterior environment
kernels from **past percept-only** likelihood products. Actions remain in the
recorded history but are not likelihood factors. Zero-denominator fallback is
a point mass at the zero percept. The terminal percept is included in trace
likelihoods without introducing an extra action. A single mixed environment
works for every policy simultaneously; finite trace/expectation mixture laws
prove full all-policy admissibility and limiting values. Eight gates passed
`1793285278607872107-6.json`.

`LatticeLimit` proves closure of `d⁻¹ℤ` under finite-real sequence limits for
positive integer `d`. `LatticeRewardLimit` applies it to **arbitrary signed
per-step lattice rewards** and their actual partial sums. No common reward
bound, convergence rate, or finite-support premise is introduced.
`DeterministicLatticeRewards F d` witnesses per-agent/environment reward
streams and convergence of their partial sums to `F.value`; it does not
presuppose that those values are in the lattice. The checked bridge derives
`LatticeValued` from this representation.

`CrossOrderObstruction` rules out cross-faithfulness with environment variation
using decreasing positive integer gaps and rational midpoint environments.
`CrossFromDeterministicRewards` composes the general reward-stream bridge
with this obstruction. This is the full-source `prop:cross` target.

Actual deterministic DD values are separately proved integer-valued, and
`scaledDD S d` is calibrated against actual finite reward sums divided by
`d` and their limits. The actual scaled-DD to stochastic-environment
specialization allows different source and target alphabets. **This scaled
specialization is not claimed to exhaust the general source domain.** The
five lattice/calibration gates passed `1793285511351278033-6.json`; all four
obstruction/closure gates passed `1793285539025721274-6.json`.

## Historical first-stage freeze and ownership

The initial definitions/targets passed `1793275758735001426-6.json` and were
frozen in the task review record `rl-policy-frozen-before-proof.json` before
candidate authoring. Initial accepted candidate hashes were:

- `PolicySemanticsProof.lean`:
  `588c171650bccf9383f6dc8f329a1e20930a2e8f19ecb70d193f16ad2e2632de`.
- `AffineProof.lean`:
  `c57a7e09063d07b7754a6584a6e3ef21ced8ae3a7b8f56eb83026f7be1f33fb0`.

Subsequent bundles retain their own independent freeze and acceptance records.
The final source-general cross acceptance is recorded in task review artifacts
`rl-cross-lattice.json`, `rl-environment-mixture.json`, and
`rl-cross-obstruction.json`; classification acceptance is `rl-classification.json`.
These names identify review provenance, not portable repository file links.

No numbered paper-13 source target remains unproved in this lane after the
above independent acceptance. Root still controls public integration and any
whole-project completeness/publication claims. Other papers, alternative
transformation contracts, effective/injective conversion requirements, and
unrestricted rational reward lattices are not covered by this result.
