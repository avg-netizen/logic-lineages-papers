# Bounded continuation: raw lambda dynamics and chosen common knowledge

This continuation starts from `73709637b4997891d26ad5651628a44a8ac38392` on
`formalization/cumulative-continuation-2026-11-16`. Its two proof packets are
independently checkable without the Paper 6 accessibility import closure.
The original numbered register remains **178 checked, 2 inherited, 9 pending
out of 189**.

Both packets are accepted after native exact-type and axiom checks, independent
final review, and a recursive source/object/log audit. Together they provide
five frozen exact contracts in two substantive proof advances.

| Packet | Exact contracts | Local module closure | Peak process-tree RSS |
|---|---:|---:|---:|
| Raw lambda dynamics | 2 | 18 | 802,508 KiB (783.7 MiB) |
| Chosen common-knowledge transport | 3 | 282 | 1,090,596 KiB (1,065.0 MiB) |

The combined closure contains 299 distinct local modules. All 14 frozen pins
match, all five exact alias audits are present, and the recursive evidence
reports zero errors. See [the acceptance record](ACCEPTANCE.json).

## Raw lambda dynamics

The original typed `RawStep` and `RawSteps` relations satisfy two exact laws:

1. A finite raw path from `lam body` ends at same-type bottom, or at `lam next`
   with a finite raw path from `body` to `next`. Conversely, each alternative
   gives the stated lambda path, including the zero-step case.
2. Accessibility for descending raw reduction holds at `lam body` exactly
   when it holds at `body` in the extended context.

The proofs retain arbitrary symbols, arities, precedence, contexts and types.
They use lambda-step inversion, bottom terminality, finite-path induction and
accessibility induction. These are native suppliers for the lambda argument
under Paper 6 `lem:id1`. Internal certificate transport, quotient/canonical
fold compatibility and the complete internal accessibility theorem remain
separate obligations.

See [the frozen contract and source review](raw-lambda-dynamics/REVIEW-PREFLIGHT.md),
[the final independent review](raw-lambda-dynamics/REVIEW-FINAL.md), and
[the native receipt summary](raw-lambda-dynamics/NATIVE.json).

## Chosen common-knowledge transport

For the same actual source D, chosen common-knowledge tag and existing internal
HB2/HB3 evidence, an ordinary D proof of `sigma -> tau` produces an ordinary D
proof of `CK_A(sigma) -> CK_A(tau)`, for every full-language sentence pair and
selector. The proof constructs `Pr_D(delta) -> delta` for that implication,
using selected reflection/distribution and both original fixed-point instances,
then applies the existing Lob reduction. The temporary premises are discharged
before invoking the theorem rule.

The second exact contract supplies the missing ordinary implication from
`literalTheta` to `sourceTheta` in every ordinary theory. Equality reflexivity
discharges the top-selector `x=x` guard. Together with the existing reverse
implication, the third contract derives common-knowledge equivalence for these
two distinct sentences at the same chosen tag. No AST or Godel-code equality
is asserted.

This is conditional supporting progress toward the unnumbered displayed
`eq:counterexample` in Paper 12. Specializing to the existing same-source HB
witness and assembling the literal KT negation/nonprovability result remain
outside this packet. All six numbered Paper 12 statements were already checked.

See [the frozen contract and source review](chosen-common-knowledge-transport/REVIEW-PREFLIGHT.md),
[the final independent review](chosen-common-knowledge-transport/REVIEW-FINAL.md),
and [the native receipt summary](chosen-common-knowledge-transport/NATIVE.json).

## Reproduction

From `formalization`, with the pinned Lean toolchain and official targeted
Mathlib cache available, run these gates sequentially:

```bash
python3 scripts/check.py --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048 \
  LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawLambdaDynamics.StatementChecks

python3 scripts/check.py --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048 \
  LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.ChosenCommonKnowledgeTransport.StatementChecks
```

Each packet separates the target propositions, expanded comparator and proof.
The targets and comparator hashes were frozen before proof authoring; both
comparator gates passed before their candidate proofs were written. Exact
statement aliases and namespace audits check the actual kernel axiom closures.
The 14 entries in `FROZEN.sha256` also protect the original source suppliers,
register, checker and toolchain/dependency pins.

The unchanged checker uses one worker, a 2048 MiB heap cap, 1536 MiB process-tree
RSS cap, 2048 MiB free-memory floor, and 90 CPU/180 wall seconds per module.
`SETUP.json` records the official pinned compiler and targeted cache restoration.
No full Paper 6, aggregate-root or remote-CI build is claimed. The first lambda
draft and its single constructor-qualification repair are preserved separately
from the accepted source.
