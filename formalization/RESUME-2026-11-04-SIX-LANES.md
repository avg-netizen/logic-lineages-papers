# Resume: Sol supervises Claude, plus five independent Sol lanes

The user explicitly resumes formalization and requests one Claude lane
supervised by Sol, plus five independent GPT-6.1 Sol lanes at xhigh effort.
Sol is the supervisor; Claude is the read-only proof author. This release
supersedes the completed R026 and independent-lane stop ceilings only for the
public-paper formalization programme. All unrelated research remains paused.

The source baseline is local commit `ba9237a98a20e24a87c2c95e91df67a185c11511`
on `formalization/reconcile-unpublished-2026-11-04`. Read
[the completion audit](audits/PENDING-STATEMENTS-2026-11-04.md) and the current
`TARGETS.json`: 155 checked, 2 inherited, 32 pending out of 189. Recovered AG
proofs are present. GroundLambdaTower1 and ZeroPatternSubstitution3 remain
independently unreviewed until a lane explicitly checks their exact scope and
gate; archive inclusion alone is not acceptance. No new fetch/push, main merge,
toolchain/dependency change or CI reconfiguration is authorized by this release.

## Allocation and ownership

| Lane | Model | Original endpoint | Exclusive new source home |
|---|---|---|---|
| C: Sol supervises the same Claude session | GPT-6.1 Sol xhigh supervisor; existing Claude Opus5.5/high author | Paper12 source-Base correspondence for `lem:three` and `thm:consistency`, then the actual collapse chain | `LogicLineages/ComputabilityKnowledge/SourceBaseCompletion/` |
| S1: simulation | GPT-6.1 Sol xhigh | Paper06 `lem:simulation`: one actual fixed-S computable translation and positive quotient simulation | `LogicLineages/OrdinalComparison/TerminationOrdering/SourceSimulationCompletion*` |
| S2: ID1 | GPT-6.1 Sol xhigh | Paper06 `lem:id1`: actual internal accessibility proof and typed computability/fundamental obligations | `LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/` |
| S3: arithmetic decision | GPT-6.1 Sol xhigh | Paper08 `thm:snyatkov`: full multi-variable/quantified BASE decision | `LogicLineages/OrdinalComparison/LayeredComparison/SnyatkovCompletion/` |
| S4: kernel source completion | GPT-6.1 Sol xhigh | Paper08 kernel/counter/residue source correspondence and valid signed-domain contracts | `LogicLineages/OrdinalComparison/KernelSourceCompletion/` |
| S5: functional hardness | GPT-6.1 Sol xhigh | Paper09 `thm:functional-hardness`: polynomial-system undecidability and exact actual-source reductions | `LogicLineages/OrdinalComparison/FunctionalHardnessCompletion/` |

Each lane owns its matching evidence subdirectory under
`verification/local-resume-2026-11-04-six-lanes/`. Main owns shared root imports,
`TARGETS.json`, source adoption, aggregate integration, shared compiler policy,
Git and cross-lane coordination. Existing accepted files are read-only; propose
necessary shared changes to main. No additional agent or proof stream is
authorized. Run continuing coherent rounds until the user changes the release;
a small supplier is a checkpoint, not an automatic reason to stop the lane.

## Sol-supervised Claude lane

Resume the SAME existing session `ac0922e0-cd7e-4974-8079-7a9c70779735` using
the reviewed `FORMALIZATION-2026-10-31/run_round.py` runner and the unchanged
Claude Opus5.5/high/Read-Glob-Grep contract. R026 is the last complete round;
the next is R027. Sol independently chooses and freezes source-preserving
definitions/targets, obtains their successful pre-author comparator build,
and records pins before Claude authors proof steps. Sol then compiles the
returned candidate first, constructively repairs diagnostics or exact-statement
mismatches, and audits actual transitive axioms before accepting a result.

Keep all historical pause/acceptance records immutable. The supervisor may
clear the completed R026 current author admission/pause controls under this
explicit release, with before-snapshots and a new release receipt. Do not create
a substitute author/model/session. Report actual initialization and source reads
before saying Claude is running. Other author subjects remain paused.

The immediate paper12 gap is the exact source PA(L)/definitional syntax Base
and its proof/model correspondence. Do not make internal HB/Lob an extra
prerequisite for `lem:three` or the revision consistency proof. Existing selected
logic, actual KT/FS/UBF proof rules and revision machinery must be reused.

If Claude reaches a usage limit, Sol finishes repair/checks/feedback for an
already returned candidate, then waits for the exact reset and resumes the SAME
pending round/session. With no candidate, save state and wait directly. No
independent mathematics or alternate author in lane C during that wait. The
five independently authorized Sol lanes may continue.

## Source completion and acceptance

Freeze the entire exact target before proof authorship. Keep definitions and
comparison types separate from proofs; preserve scope, semantics, quantifiers,
source hashes and effectivity claims. No sorry/admit/native_decide/new axioms
or assumed decision/accessibility/provability suppliers. Actual axiom closures
may use only propext, Classical.choice and Quot.sound. Do not report a restricted
or conditional component as a whole printed statement.

S4 must expose proposed source repairs and their mathematical effect explicitly
to main before changing a manuscript or source register. Preserve the old
printed contracts and checked negative evidence. The paper08 whole-state versus
limit-part process and negative degree-one depth defects must not be hidden by
a larger cutoff, clamping, a new convention or an unannounced weaker target.
For a complete existing theorem under the intended convention, prefer an exact
source bridge over re-authoring its component proofs.

## Single compiler queue

All six lanes share ONE native compiler. Before every native check, message
main with lane, requested module(s), purpose (target preflight, candidate or
exact gate), and profile. Wait for main's explicit compiler-slot grant. The
slot is held until the native process is fully reaped and its result/receipt
reported. A busy lock is not permission to bypass the queue or raise limits.

Only `python3 scripts/check.py` from `formalization/` may compile. Use the
existing single-worker 2048 MiB heap / 1536 MiB RSS / 2048 MiB free-memory
profile, 90 CPU / 180 wall seconds per module, pinned upstream cache and both
existing shared locks. No cold upstream build or resource-limit increase.
Claude read-only author overlap follows its existing >=3072 MiB admission
policy and 512 MiB observed RSS cap; a serialized author holding native locks
must be reported to main and waited for. The increased model-agent count does
not authorize more compiler processes.
