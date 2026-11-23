# Opus B ledger — round 2 (append-only)

All paths are relative to `formalization/`. Gate: `verification/local-fable-pair-2026-11-22-round2/gate.sh`.

## Part 1 — joint near-control closed-block decision (prefix `UniformNearClosedBlock`, unused before)

- Parametric effectivity helper modules (proof-only, generic lemmas):
  - `UniformNearClosedBlockEntryProof`: step, states, test, bounded index, scan.
    - v1, a single file, was killed at the 90 s CPU cap (receipt `1795396910867291828-3228823`). The draft is kept.
    - Split into three files and the heavy table definitions made locally irreducible; it then PASSED: receipt
      `1795397326730841646-3231875`.
  - `UniformNearClosedBlockScanProof`: search, scan program, closed scan. PASSED with the next one.
  - `UniformNearClosedBlockFieldProof`: iterate, entry result, value field, count field.
    - Failed twice on a whnf timeout and a stuck instance (receipts `1795397340946521434-3231960`,
      `1795397402294203628-3232341`). Then PASSED: receipt `1795397415231054253-3232412`.
- 2026-11-23T01:31Z: Targets frozen: `UniformNearClosedBlockTargets.lean` sha256 `0473f56e…fac3`, receipt
  `1795397439900681705-3232524`. Source map `opusB/UNIFORM-NEAR-CLOSED-BLOCK-SOURCE-MAP.md`.
- Root (message): `uniformImpliesGround` and `uniformMainFromGround` are already gated (#1437). My remaining Part 2
  goal is exactly `UniformGroundComparison`.
- `UniformNearClosedBlockSliceProof` PASSED: receipt `1795397525165634837-3233010`.
- `UniformNearClosedBlockDriverProof` PASSED on the first attempt: receipt `1795397630588805580-3233688`. Gives
  `parametricSolveEffectivity`.
- `UniformNearClosedBlockProof` v1 FAILED on missing imports (receipt `1795397665700092748-3233970`). v2 PASSED:
  receipt `1795397679846287297-3234101`.
  - Gives `nearDecideComputable`, `nearDecideExact`, `uniformNearClosedBlockDecision` and `fullUniformNearClosedBlock`.
  - All axioms are standard.
- `UniformNearClosedBlockJointProof` PASSED: receipt `1795397699271029203-3234272`. It proves
  `jointNearClosedBlocks : UniformGroundAssembly.JointNearClosedBlocks`, root's frozen def, by `exact`.
- Root reassigned all of Part 2 to itself. I wrote no Part 2 material: no `UniformGroundAssembly*`,
  `UniformGroundDecidable` or `UniformNearGroundDecidable` module.
- No ingredient was found that fails to be jointly computable in `b`. Evidence:
  `opusB/UNIFORM-NEAR-CLOSED-BLOCK-EVIDENCE.json`. Nothing is drafted and ungated.

## P16 gap map (reading deliverable, 22 Nov)

- Wrote `opusB/P16-GAP-MAP.md`: all eight pending Paper 16 labels mapped to records/notes, classified, ranked.
- Measurements only: `import_graph.py closure` on native realization/iteration/rank modules, greps over
  legacy-closure sources and record scopes. No gate run, no `.lean` file written or edited.

## Module-system twin pilot (Root task, 22 Nov)

- Generator `opusB/twin/make_twins.py`; manifest `opusB/twin/TWIN-MANIFEST.json`. Twins under
  `LogicLineages/NativeModule/` (new untracked files; no original touched).
- Pilot A generated: 22 twins for `NativeIteratorStrictTargets` closure, 0 body changes.
- Pilot A GATE PASSED (mathlib profile): receipt `1795398779920166780-3252793`. 22 modules, all compiled
  (no cache), peak RSS 310,428 KiB (DecisionInventory), sum 15.76 s wall / 12.01 s CPU, 0 body changes.
- Pilot B GATE PASSED: receipt `1795398823698366488-3253188`. 140 modules (138 twins compiled fresh, 2
  module-system originals + 21 earlier twins verified cache hits), sum 215.37 s wall / 177.6 s CPU, 0 body changes.
  Peak RSS 869,888 KiB at twin `NativeOrdinalIterationTargets` (mixed root: twin native closure +
  module-system `OrdinalRealizationTargets`/`OrdinalNativeIterationTargets`). Twin `NativeOrdinalRealizationTargets`
  864,672 KiB vs legacy original 1,573,864 KiB stop; cap 1,572,864 KiB → headroom 708,192 KiB (45%).
  The Mathlib ordinal module alone costs 849,936 KiB; the twin native layer adds ~15–20 MB.
- Iteration proof closure: 653 twins generated. Gate 1 FAILED at twin `NumberedWindowExternalApplication`
  (receipt `1795399074444699902-3255016`): private `applyRepresentative` referenced from an exposed public def
  body ("would need to be public to access here"). All earlier modules passed (now cache hits).
  `twin/private_scan.py` finds 8 files / 9 private defs referenced from the public interface (5 predicted +
  3 exposed-def-body cases). Each fixed by deleting the one word `private` (BODY_EDITS in make_twins.py,
  diffs in manifest). 8 bodies changed, 645 unchanged.
- Iteration specialization GATE PASSED: receipt `1795399156663919873-3256109`, root twin
  `LogicLineages.NativeModule.PersistentMarking.NativeOrdinalIterationProof`. 660 modules (653 twins; 502
  compiled this run, 158 verified cache hits from Pilot B and the failed gate 1), sum 593.98 s wall / 500.69 s
  CPU this run. Peak RSS 929,556 KiB at the root (cap 1,572,864 KiB; headroom 643,308 KiB, 41%).
  Theorems (declaration names unchanged from the drafted legacy originals):
  `LogicLineages.PersistentMarking.NativeOrdinalIterationProof.exact_NativeIteratorRealizesFullPrefix :
  NativeIteratorRealizesFullPrefix` and `exact_NativeIndexedCarrierOrbit`, axioms [propext, Classical.choice,
  Quot.sound]. The closure also gated the twin `NativeOrdinalRealizationProof` (921,748 KiB):
  `exact_NativeRealizationClosure`, `exact_NativeLambdaRealization`, same axioms. No sorryAx in the log.
  Twin bodies: 645 byte-identical, 8 with the one-word `private` deletion. Manifest re-hash: 0 mismatches.
  Stopped here as instructed (no `lem:realization` work beyond its proof module being in the closure).
- Rule slip: during the gap-map and pilot work I ran read-only git commands (`git log`, `git ls-files`,
  `git status --porcelain`, an empty `git diff --no-index`) to check tracking/untouched state. Nothing was
  written via git; reported to root.
- The 8 twins that failed in gate 1 were regenerated in place by `make_twins.py --refresh`. Their failed
  versions are exactly the generator output with empty BODY_EDITS (header + original body), so they are
  reproducible from the originals and were not separately kept.

## Native rank wrapper on the twins (Root task, 22 Nov)

- Root: twin pilot recorded as #1446 (iteration) and #1447 (realization). Tracked state is now checked
  only by `ls` / hash comparison with the manifest (no git).
- Drafted rank modules found in the tree (legacy, never gated as a whole; frozen copy of the stopped
  edition in `recovery-nov19/native-rank-local-native/1795138515409234140-10/`, stop at
  `NativeRankOrderTargets` 1,578,436 KiB, rc 77):
  `NativeRankTargets`, `NativeRankGlobalTargets`, `NativeRankOrderProof`, `NativeRankCountabilityProof`,
  `NativeRankChecks` (with `compose`), `NativeRankOrderTargets/Checks`, `NativeRankPrefixTargets/Checks`;
  #522's wrapper = `NumberedWindowConfinedRankDominanceTargets/Proof` (closure 434, 430 legacy).
- Twins generated for those roots plus `NativeSyntaxCountabilityChecks` and
  `NativeClosedStrictWellFoundedChecks`: closure 454 (450 legacy), 18 new twins, manifest 671, still 8
  body changes (same private sites; no new ones by `private_scan.py`).
- Frozen targets (twin sha256): `NativeRankGlobalTargets` edfeefe1…a774, `NativeRankTargets` 9e832681…a0,
  `NumberedWindowConfinedRankDominanceTargets` 3e98249a…a37f.
- New assembly (not a twin): `LogicLineages/NativeModule/PersistentMarking/NativeRankUnconditionalChecks.lean`,
  `exact_ActualClosedNativeRanks` = `compose` applied to the three checked suppliers.
- Rank gate 1 (receipt `1795399748659677836-3263981`): #522 wrapper PASSED — twin
  `NumberedWindowConfinedRankDominanceProof` (`exact_ConfinedRankBelowFixedQuote`,
  `exact_OriginalInitialQuoteRankDominance`, axioms [propext, Classical.choice, Quot.sound]), peak RSS
  906,532 KiB. Twin `NativeRankOrderTargets` 852,496 KiB (legacy stop 1,578,436). Then FAILED at twin
  `NativeRankOrderChecks`: the drafted proof itself does not elaborate (relations of
  `exact_RankOfRelationMap` not inferable through `Subtype.val`). Repaired in the twin (named arguments
  `r`, `s`; BODY_EDITS + diff in manifest). Prefix and unconditional modules not reached.
- Rank gate 2 (receipt `1795399824264854463-3264483`): twin `NativeRankOrderChecks` (repaired), 
  `NativeRankPrefixTargets/Checks`, `NativeRankTargets`, `NativeRankGlobalTargets`, `NativeRankOrderProof`
  PASSED; FAILED at twin `NativeRankCountabilityProof`: drafted proof cites `Ordinal.isSuccLimit_omega`,
  absent from pinned Mathlib; the lemma is `Cardinal.isSuccLimit_omega`. Repaired (qualifier only).
- Rank gate 3 PASSED: receipt `1795399872966250102-3264833` (455 modules, 451 twins; all four requested roots).
  Peak RSS 916,296 KiB at new `NativeRankUnconditionalChecks` (headroom 656,568 KiB). Gated, axioms all
  [propext, Classical.choice, Quot.sound], no sorryAx:
  `NumberedWindowConfinedRankDominanceProof.exact_ConfinedRankBelowFixedQuote`, `…exact_OriginalInitialQuoteRankDominance`
  (906,532 KiB); `NativeRankOrderChecks.exact_NativeRank{Recurrence,StrictEdge,Restriction,SuccessorWitness}` (854,740);
  `NativeRankPrefixChecks.exact_CountableNativeRankPrefixes` (856,456); `NativeRankChecks.exact_*` and `compose` (871,160);
  `NativeRankUnconditionalChecks.exact_ActualClosedNativeRanks` (no hypothesis).
  Manifest: 671 twins, 10 bodies changed (8 one-word `private`, 2 proof repairs), re-hash 0 mismatches.
- Gap map §5 updated (thm:upper). Parked drafts (Mathlib in a legacy closure, no accepted pin, no passing local
  receipt) listed in the report to root; none started.
