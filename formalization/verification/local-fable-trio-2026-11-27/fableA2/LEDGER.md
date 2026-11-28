# Fable A2 ledger — ordinal calibration lane, uniform induction over the type level (27 November 2026)

(append-only; continues `../fableA/LEDGER.md`)

## Entry 1 — reading done, plan written

- Read BRIEF.md, `fableA/LEVEL-L-NOTE.md`, `fableA/LEDGER.md` (Entries 1–11), `STEP-CALCULUS-SOURCE-MAP.md`,
  the levels targets/proofs, the step/orbit/level-two modules, `NativeTowerTargets` 60–100.
- Plan: `fableA2/UNIFORM-INDUCTION-PLAN.md`. Decisions: flat (environment) form of the logical relation;
  `ExpSep` with `|σ|` in clause 3 (weights are not countable above level 2); one bound at the bottom of the chain;
  new side condition found on paper at type `A_3`/`A_4`: `ExpSep s 0` (`|s| ≤ |s+1|`) for the weight `s` of the
  argument of `B_m`. No induction on the level is needed for "B_m has weight 0": it is one argument for all `m ≥ 1`.
- Nothing gated yet.

## Entry 2 — function-side targets frozen; family lemma gated (first attempt)

- Frozen: `LogicLineages/NativeModule/PersistentMarking/ActualCalibrationUniformTargets.lean` (defs `appDown`, `domClause`, `GoodAt`, `GoodEnv`, `GoodF`,
  `GoodFamily`; statements `FamilyDiagonal`, `OrbitGood`, `TowerGood`). sha256
  `6112be372146d4fbea819ab14f3eb11ab2fdbb8ec88e1e6b351090c4e5cf7848`.
- Gate 1 **PASS**, receipt `1795815470684857486-1099377` (log `fableA2/gatelogs/gate1.txt`):
  `ActualCalibrationUniformTargets`, `ActualCalibrationUniformFamilyProof` — `familyDiagonal : FamilyDiagonal`
  (plus `fam_mono`, `fam_strict`, `fam_lt`, `fam_diag_id_le`, `fam_fix_limit/closed/crit`, `fam_spec`,
  `fam_b0_lt`, `fam_fix_good`). Standard axioms. sha256 of the proof module
  `7598dfba2dfd164ac55220161d688a9aa8f2d04278d4cbc5df626ad1e145bb9f`.
- Drafted, gate 2 running: `ActualCalibrationUniformGoodProof` (`orbitGood`, `towerGood`, env calculus,
  `appDown_tower`).

## Entry 3 — function side at every type level gated

- Gate 2 **FAIL**, receipt `1795815676172335605-1100700` (log `fableA2/gatelogs/gate2.txt`):
  `ActualCalibrationUniformGoodProof` — three sites used `Function.update_of_ne (by omega) G xs` with the value
  explicit; Lean then infers the dependent family from `G`'s type (`α := FiniteType`). Not a mathematical
  failure. Failed draft kept: `drafts/fableA2/ActualCalibrationUniformGoodProof.gate2-failed.lean.txt`.
- Gate 3 **PASS**, receipt `1795815845408612238-1101794` (log `fableA2/gatelogs/gate3.txt`):
  `ActualCalibrationUniformGoodProof` — **`orbitGood : OrbitGood`** (orbits of a good object from a good
  object are good, every type), **`towerGood : TowerGood`** (every `B_m` is good), plus `appDown_congr`,
  `appDown_update`, `semDown_appDown`, `appDown_sup`, `goodEnv_congr/update/le`, `good_app`, `goodF_app`,
  `goodFn_sup`, `orbit_family`, `appDown_tower`, `appDown_tower_succ`. Standard axioms. sha256
  `c52996bc1bc65158b87d3b81575d1433971836a467fb176f6c161df3f306af01`.
- Next: weight targets (`ExpSep`, `expDown`, `CondDown`, `WEnv`, `WeightF`, `DiagFam`, `LimFam`; statements
  `OrbitWeight`, `TowerWeight`, `AllLevels`), norm calculus at arbitrary exponents + family lifting.

## Entry 4 — status of the files root asked about; weight targets frozen; norm calculus and family lifting gated

(Session was stopped by an account limit between starting gate 4 and writing this entry; root released it.)

Status of the three files root listed as having no receipt:
- `LogicLineages/NativeModule/PersistentMarking/ActualCalibrationUniformFamilyProof.lean` — **gated proof module**, not a draft: gate 1, receipt
  `1795815470684857486-1099377` (Entry 2).
- `LogicLineages/NativeModule/PersistentMarking/ActualCalibrationUniformWeightTargets.lean` — **frozen targets** (definitions `ExpSep`, `expDown`,
  `CondDown`, `WeightAt`, `WEnv`, `WeightF`, `DiagFam`, `LimFam`; statements `FamilyLifting`, `OrbitWeight`,
  `TowerWeight`, `AllLevels`). sha256 `d9009214487c4a8b4bea6fdff505f5c4d56a6a0c080338ff4bbfeb7956c88159`.
  Compiled in gate 4 below. It does not change from here.
- `LogicLineages/NativeModule/PersistentMarking/ActualCalibrationUniformNormProof.lean` — proof module, was an ungated draft when the session stopped;
  **gated now** (gate 4).

- Gate 4 **PASS** (first attempt), receipt `1795816095108793665-1103069` (log `fableA2/gatelogs/gate4.txt`):
  `ActualCalibrationUniformWeightTargets`, `ActualCalibrationUniformNormProof` —
  **`familyLifting : FamilyLifting`**, `diagFam_base`, `limFam_base` (base families `a ↦ σ' + Ω^σ·a`), plus
  `nsepG_norm_mul`, `nsepG_step`, `normG_div_le`, `normG_ge_of_mul_le` (arbitrary exponents below Λ),
  `sep_opow/sub/ge/lt`, `diagFam_lift`, `limFam_lift`, `le_expDown`, `condDown_bound/opow_lt/lt/mono`,
  `expSep_mono`, `expSep_zero`. Standard axioms. sha256 of the proof module
  `0bc1e7c5befd1ff158a195722bd4c1b479744c017a487bcce31dbfa19815e830`.
- Source map for both target modules: `fableA2/UNIFORM-SOURCE-MAP.md` (written with this entry).
- Ungated at this point: nothing on disk. Not yet written: `…UniformWeightProof` (`orbitWeight`, `towerWeight`),
  `…UniformLevelProof` (`allLevels`), `ActualCalibrationAllProof`.

## Entry 5 — gate 5 did not compile anything (wait timeout); drafts on disk

- Gate 5 **NO RESULT** (`GATE_WAIT_TIMEOUT rc=75`, log `fableA2/gatelogs/gate5.txt`): the machine memory gate stayed
  closed for the whole 1500 s wait (1.2–1.9 GiB available, 2048 required; an Android emulator, a VM and another
  project's Lean build were resident). No compiler was launched; not a failure of the module.
- Ungated drafts on disk at this point (all three written, none compiled yet):
  `ActualCalibrationUniformWeightProof.lean` (`orbitWeight`, `towerWeight`),
  `ActualCalibrationUniformLevelProof.lean` (`allLevels`),
  `ActualCalibrationAllProof.lean` (`allTowerCalibration`, `calibrationAt_five`).
- Re-running as gate 6 with a longer wait, the three modules in one call.

## Entry 6 — pause requested by root; state while gate 6 is still waiting for memory

Root's message (about 20:50 CST): the 2048 MiB free-memory floor has not been met since about 20:14; let the
current gate call (gate 6, started 20:19, wait limit 3300 s) run to its deadline, start no further wait, start no
new layer. This entry is written while gate 6 is still waiting, so that the state is on disk whatever happens;
the verdict of gate 6 is in Entry 7.

### Module status

| module | kind | status | receipt |
|---|---|---|---|
| `ActualCalibrationUniformTargets` | frozen targets | GATED | `1795815470684857486-1099377` |
| `ActualCalibrationUniformFamilyProof` | proof (`familyDiagonal`) | GATED | `1795815470684857486-1099377` |
| `ActualCalibrationUniformGoodProof` | proof (`orbitGood`, `towerGood`) | GATED | `1795815845408612238-1101794` |
| `ActualCalibrationUniformWeightTargets` | frozen targets | GATED | `1795816095108793665-1103069` |
| `ActualCalibrationUniformNormProof` | proof (`familyLifting`, `diagFam_base`, `limFam_base`) | GATED | `1795816095108793665-1103069` |
| `ActualCalibrationUniformWeightProof` | proof (`orbitWeight`, `towerWeight`) | **UNGATED** (never compiled) | — |
| `ActualCalibrationUniformLevelProof` | proof (`allLevels`) | **UNGATED** (never compiled) | — |
| `ActualCalibrationAllProof` | proof (`allTowerCalibration`, `calibrationAt_five`) | **UNGATED** (never compiled) | — |

sha256 of the ungated drafts as they stand:
```
2d358f57e016f9a0b483855feced8ede52afde475b1cf433e0e886ba5c2e5975  LogicLineages/NativeModule/PersistentMarking/ActualCalibrationUniformWeightProof.lean
57cdecc6493a19a39980ac5f88502819380df5496b4b6e237ea55038e028a1a2  LogicLineages/NativeModule/PersistentMarking/ActualCalibrationUniformLevelProof.lean
702a8e7664fc3ebade38e939b9d6cdd772c7e2d035dfe4b08284eac699aa2d15  LogicLineages/NativeModule/PersistentMarking/ActualCalibrationAllProof.lean
```

### State and next (for a fresh session)

- **Frozen statements** (do not change): in `ActualCalibrationUniformTargets`: `FamilyDiagonal`, `OrbitGood`,
  `TowerGood` — all three PROVED and gated. In `ActualCalibrationUniformWeightTargets`: `FamilyLifting` — PROVED
  and gated; `OrbitWeight`, `TowerWeight`, `AllLevels` — proofs DRAFTED, UNGATED.
  `Paper16RemainingOrdinalTargets.AllTowerCalibration` — proof DRAFTED (one line through
  `ActualCalibrationLevelsProof.exact_AllFromLevels`), UNGATED.
- **What is established by the compiler**: the whole function side at every type level (every `B_m` is good,
  orbits of good objects are good, the good-family facts that feed `stepDiagonal`/`stepLimit`), and the whole
  norm side (norm calculus at arbitrary exponents below Λ, the chain conditions, the lifting of the index
  hypotheses of `StepDiagonal`/`StepLimit` along `expDown`, the two base families).
- **What remains of the uniform induction**: only assembly, all of it written. (1) `orbitWeight`: induction on the
  stage — successor by `weightF_app` (one `Function.update` of the weighted environment), limit by `stepLimit`
  with `familyLifting.2` + `limFam_base`. (2) `towerWeight`: `m = 0` is `stepSuccessor`; `m = n+1` is
  `stepDiagonal` on the applied-down orbit with `familyLifting.1` + `diagFam_base` and the gated family facts.
  (3) `allLevels`: tower environment weighted with all weights 0, level orbit of weight `e`, then the
  empty-context argument of `psiO_tower_two` with `|towerIndex l e| ≤ e` from `exact_TowerIndexFacts`.
  No mathematical obstacle was found; the uniform statement did not break anywhere on paper
  (`UNIFORM-INDUCTION-PLAN.md` §4–5) and every analytic ingredient is gated. The risk left is elaboration only
  (the three drafts are about 640 lines that have never been through Lean).
- **Next action**: run, from ROOT,
  `bash verification/local-fable-trio-2026-11-27/gate.sh mathlib LogicLineages.NativeModule.PersistentMarking.ActualCalibrationUniformWeightProof LogicLineages.NativeModule.PersistentMarking.ActualCalibrationUniformLevelProof LogicLineages.NativeModule.PersistentMarking.ActualCalibrationAllProof`
  and repair elaboration errors in order (Weight first; Level and All depend on it). Known style traps met so
  far: `Function.update_of_ne` needs the value as `_` or an ascribed result type (use `env_update_ne` /
  `ss_update_ne`); state `show` forms with `k + 2` literals exactly as the lemma to be rewritten states them.
- If the uniform weight proofs resisted beyond elaboration (not expected), the fallback is level 3 explicitly:
  instantiate the drafts at `n = 1` (`towerWeight 2`, `orbitWeight` at `k = 2`), which gives `CalibrationAt A 5`.

## Entry 7 — gate 6 never got memory; round paused; hand-back

- Gate 6 **NO RESULT** (`GATE_WAIT_TIMEOUT rc=76` at 21:14 CST after 3300 s, log `fableA2/gatelogs/gate6.txt`,
  `CACHE_HIT` lines filtered out of the log): the free-memory floor was never met (0.8–2.0 GiB available against
  2048 MiB) and the compiler lock was mostly held by another serialized job. No compiler was launched on any of
  the three modules. Nothing can be said about them from the compiler.
- Per root's pause instruction no further gate was started and no new layer was begun.
- **UNGATED** (unchanged since Entry 6, same sha256): `ActualCalibrationUniformWeightProof.lean`,
  `ActualCalibrationUniformLevelProof.lean`, `ActualCalibrationAllProof.lean`.
  `OrbitWeight`, `TowerWeight`, `AllLevels`, `AllTowerCalibration` are therefore **not theorems yet**.
- Evidence files for the gated results (sha256 checked against the receipts): `fableA2/UNIFORM-FAMILY-EVIDENCE.json`,
  `fableA2/UNIFORM-GOOD-EVIDENCE.json`, `fableA2/UNIFORM-NORM-EVIDENCE.json`.
- Gates in this lane: 1 PASS, 2 FAIL (elaboration, repaired), 3 PASS, 4 PASS, 5 and 6 no result (memory).
  Five new modules gated, three drafted and ungated. No existing `.lean` file edited; nothing deleted; no Git.
  Nothing written outside ROOT.
- State and next: Entry 6, unchanged.
