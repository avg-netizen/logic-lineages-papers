Local workers paused at the user-requested 10 p.m. America/Chicago cutoff (30 October 2026 03:00 UTC). No automatic local resume. Separately authorized external work and fresh-clone builds remain possible.

# Formalizing the public papers

Local workers were **explicitly resumed by the user on 29 October 2026** after
the external continuation. Two independent Codex lanes, a Codex-led Claude loop
and main continue from [the external checkpoint](EXTERNAL-CONTINUATION.md).
Older pause records are historical. This is an
incomplete formalization programme for all fifteen papers in this repository.
The [target register](TARGETS.json) records 178 numbered
theorem/lemma/proposition/corollary statements from the full TeX input closure,
plus algorithmic and cited-supplier obligations. The [source snapshot](MANUSCRIPT-SNAPSHOT.json)
pins the 39 manuscript/build-source files read by that inventory. A count is
not a proof-coverage claim.

The calculator's existing checked development is a baseline dependency. Other
papers are not considered formalized merely because their definitions or an
intermediate lemma compile. Every full target remains pending until its actual
statement and complete dependency chain are checked.

## External continuation

See [the external continuation checkpoint](EXTERNAL-CONTINUATION.md) for new
accepted results, precise coverage and verification limits. Historical local
pause records remain preserved; this is a separately authorized continuation.

## Acceptance rule

1. Codex writes the exact mathematical semantics and comparison statement,
   checks their correspondence with the source, compiles them and freezes
   their hashes before Claude authors proof steps.
2. Claude's candidate proof source is separate from the frozen comparator.
   A candidate cannot edit that comparator, add missing suppliers as premises,
   or prove a surrogate model instead.
3. Compile first. Repair compiler errors or statement mismatches. A clean build
   proceeds to the exact type gate and actual axiom-closure check; it does not
   routinely receive a second hand proof audit.
4. The gate must check the candidate at the fixed type. Accepted proof closures
   may contain only the ordinary `propext`, `Classical.choice` and `Quot.sound`
   foundations. No `sorry`, `admit`, added axiom, `native_decide`, or assumed
   correctness/typeclass supplier is permitted.

A theorem's genuine hypotheses remain hypotheses: for example the ultrafilter
theorem assumes an idempotent ultrafilter near zero, exactly as in the paper.
That is different from assuming the witness or theorem which the paper proves.
Cited theorems absent from Mathlib are formalization work, even when they were
legitimate bibliographic dependencies in the prose paper.

## Work streams

| Stream | Papers | Owned modules |
|---|---|---|
| Ordinal/comparison lane | 04–10 | `LogicLineages/OrdinalComparison/` |
| Model theory and algebra lane | 01, 15 | `LogicLineages/ModelsAlgebra/PGroups/`, `Differential/` |
| Codex-led Claude loop | 02, 12, 14 | `LogicLineages/ComputabilityKnowledge/` |
| Main research and integration | 03; completed 11/13; package and shared gates | `LogicLineages/ModelsAlgebra/Forests/`, `Ultrafilters/`, `RL/` |

The [status directory](status/) contains each stream's concrete proof-to-paper
map. This programme does not resume unrelated mathematical research.

## Pinned libraries and compilation

The package uses Lean `v4.32.0-rc1`, Mathlib commit
`360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`, and the calculator package included
at `../04-pure-r1-calculator/lean`. No private repository is a public source
dependency. Standard setup with Lake is:

```sh
lake update
lake exe cache get
lake build +LogicLineages
```

The committed manifest pins dependencies. On this shared research machine,
use the bounded runner instead of starting independent Lake builds:

```sh
python3 scripts/check.py LogicLineages.RL.StatementChecks
```

The runner uses the pinned dependency cache already present in this package
or in the included calculator's development checkout. It never downloads or
rebuilds upstream libraries. Local development may borrow previously compiled
calculator objects; receipts report that choice. `--fresh` recompiles the
included local dependency closure, including calculator source, when resources
permit. Fresh source compilation is distinct from borrowing those objects.

All workers share a nonblocking lock with the existing calculator helper.
The default compiler has one thread, a 1,536 MiB managed-heap allowance,
an independently monitored 1,024 MiB process-tree resident-memory cap,
90-second CPU and 180-second wall bounds, and a system-free-memory guard. Increasing the
managed allowance does not remove the physical-memory limit. The initial
768 MiB managed budget caused library-load exhaustion; a controlled standard
order import passed at about 836 MiB RSS with the revised allowance.
The later import diagnosis distinguished Lean's legacy private-import mode
from its modern exported-module mode. New project files use `module`, public
imports and exposed public declarations, avoiding unnecessary private payloads.
The longer wall allowance covers observed import waits with little CPU use;
the CPU and physical-memory limits remain separate and unchanged. A compiler
does not start below 1 GiB available memory.
No large ordinal or fast-growing numerical value is evaluated to prove
symbolic statements.

For a verified `Init`/`Lean`/`Std`-only local import closure,
`--core-profile` instead requires 768 MiB available and imposes a tighter
512 MiB process-tree RSS cap. It rejects any Mathlib or calculator import
before launching. The 256 MiB system floor, CPU limit and source/axiom checks
remain in force. A fresh bounded-multiplication source closure passed this
profile with peak RSS below 393 MiB; the Mathlib-import rejection was checked
separately. This profile does not relax the default Mathlib build guards.

Each invocation prints a unique JSON receipt path under ignored
`build-reports/`, with source hashes, results, time and peak observed RSS.
Log filenames are unique to the invocation, so later repairs preserve the
original diagnostics. A resource stop also records every compiler thread's
wait state. A measured blocked page-I/O wait is distinct from proof search;
an explicitly longer wall-only allowance does not increase the CPU or RSS cap.
Resource stops and compiler errors are not mathematical refutations and
must not be reported as accepted proofs. `LogicLineages/Audit.lean` supplies
`#audit_namespace` to inspect the transitive axioms of every theorem in a
project namespace. Fixed statement gates remain a separate requirement.

The [component workflow](../.github/workflows/paper-components-lean.yml)
compiles each accepted gate from fresh local sources and preserves receipts.
Its title and summary explicitly limit certification to those components.
Its GitHub run and artifacts record the result for the exact checked revision.

## Reuse and full dependencies

The included calculator already reconstructs the pure single-relation R1
semantics and sharp norm bounds. It is suitable for checked notation/norm
reuse. Its relation must not be confused with the simultaneous order-two
relations in older Carlson developments.

The earlier 3.1.3 project contains useful first-order syntax, proof-checking,
arithmetization and ordinal modules. A matching name is insufficient for
reuse. For example, an earlier `FiniteCollapse` is a different mathematical
construction from the norm-controlled numerical collapse in these papers.
Gorbow's DCB/FS/KT and its self-indexed provability are also different from
the knowing-machine theory in that project. Any selected source reuse must
bring a complete local import closure, attribution, source hashes and its
actual statement/axiom checks.

The largest missing bridges are visible in `TARGETS.json`: infinitary Scott
theory and algebraic classification suppliers; Carter's graph decision
theorem; full MRDP; typed path-order and ordinal-analysis suppliers;
Snyatkov's arithmetic theorem; source-realization/undecidability suppliers;
Gorbow syntax, diagonalization and Löb; exact runtime/jump classifications;
and the actual analytic/probabilistic/algebraic semantics of the new papers.
They are not supplied as assumptions in the formal target register.
