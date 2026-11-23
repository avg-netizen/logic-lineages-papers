# Opus A ledger — round 2 (times UTC−6)

## Task — uniform source compiler (prefix `UniformPolicyCompiler`, unused)

- Read `CORRESPONDENCE-REVIEW.md` §1 and §4, `PolicySuppliedCodeMacro*` (#1433/#1434) and `UniformGroundComparisonTargets`.
  I accept the correction to my round-1 `thm:main` table: "for every effective policy" does not retain the printed
  "uniformly in a supplied computable policy".
- Reading the compiler: `PolicySourceInterface.compile p d n = assignmentCode p (replicate d 0) n >>= compileVectorCode`.
  The policy enters **only** through `PolicyShape.macroCode p tag n xs`, including `repeatCode`, in `PolicyPartial`,
  `PolicyConstructors`, `PolicyAbstraction` and `PolicyAssignment`. It never enters through `Effective p` or a chosen
  witness, so the definitions are uniform in the selector.
- Bound check for technique (b): the queried arities are not syntactically bounded. In particular
  `PolicyAbstraction.coordinateCode` calls `repeatCode … scalarRepeat (factorCode level h)` with
  `factorCode = 2^(level+1)·Σ partialSize h`, where `h` is a previous macro output. So no a-priori bound is
  computable from the term code alone.
- **Technique chosen:** (b′), tabulation with on-demand extension.
  1. A generic copy of the four recursions, parametric in a finite selector table `T`. A lookup miss returns
     `Sum.inl (tag, arity)`, kept separate from rejection.
  2. Joint computability in `(T, d, c)`, re-using the existing `ComputableRankedProof.ranked` skeleton with `T`
     threaded into the recursion argument.
  3. Soundness (a sound table gives the true result whenever it does not miss) and completeness (some finite table
     of `e`'s values does not miss).
  4. A `Partrec` driver: unbounded search over `k`, tabulating `e.eval` at all `(tag < 7, arity ≤ k)`.

  Reason: every existing effectivity proof is `Computable`-based on `ranked`, so threading a table reuses it nearly
  verbatim. A direct `Partrec` lift (technique (a)) would need a new partial ranked-recursion combinator and
  partial versions of every assembly lemma.
- **Frozen** `LogicLineages/PermittedControl/UniformPolicyCompilerTargets.lean` sha256
  `5ee4f86932723be0b6ce8bf9a718da2090a0190f5c74760bfb12cd96efddd62e` (receipt `1795396681854541805-3225971`):
  `Calibrated`, `ExactUniformCompiler`. Interface for Opus B: `opusA/COMPILER-INTERFACE.md`.
- **Technique revised before any proof (the Targets above are technique-independent):** technique (a), structural, via
  Kleene's recursion theorem. Each of the two code recursions (`PolicyPartial.run`, `PolicyAssignment.assignmentCode`)
  is re-expressed as a one-step functional `Φ` over `Part (Option …)`:
  - macro calls become `macroEval` (#1433);
  - recursive calls become decoded `eval` of a code;
  - the inner folds over `List.range` become `Partrec.nat_rec`.

  `Nat.Partrec.Code.fixed_point₂` gives one fixed code, so the compiled function is `Partrec` by construction.
  Calibration on a realizing program is strong induction on the term code against the existing equation lemmas. It
  never mentions a "missing" table entry.

  Reason for the switch: (b′) needs a second full copy of the `Computable` proofs with the table threaded, plus
  soundness *and* completeness of tables. Kleene needs only one-step `Partrec` proofs and a direct calibration, with
  no new recursion combinator; the recursion is handled once, generically (`exists_fix`).
- **Frozen** layer-1 `UniformPolicyCompilerPartialTargets.lean` sha256 `661b2278ad1201b87f8f044c3d9066cfad7b47f527e95fd2a45c0074e2d98e63` (receipt `1795397337237643504-3231929`): `ExactUniformPartial`. Infrastructure `UniformPolicyCompilerFixProof` (decodeEval, `exists_fix` via `fixed_point₂`, `pbind`, `pite`) compiled, receipt `1795397134099696045-3230876`.
- Layer 1 FAIL ×3: rewriting in the calibration, and two stuck `Primcodable` instances
  (`1795397482531455684-3232830`, `1795397513097837426-3232953`, `1795397529668257934-3233046`). **Gate PASS**
  `UniformPolicyCompilerPartialProof`, receipt `1795397543874623162-3233154`: `exactUniformPartial`
  (`PolicyPartial.run` uniform in the supplied program, via `exists_fix`), standard axioms.
- Layer 2.
  - `UniformPolicyCompilerPiecesProof` first FAIL `1795397718021067277-3234392`, `1795397781536260971-3234937` and
    `1795397832867259505-3235244` (a non-Primrec `to_comp`, a whnf timeout in `applicationPartrec`, a stuck
    instance, a rewrite in `partialsCal`).
    - Fixed by a standalone `appFieldsU` and its `Primrec` lemma, and typed projections.
    - **PASS** `1795397903459563104-3235640`: constructors and abstraction lifted, each with its calibration.
  - `UniformPolicyCompilerProof` v1 (monolithic `assignStepPartrec`): whnf timeout, `1795398011336754233-3236419`.
    The calibration `assignUCal` already elaborated in that run.
  - After splitting it into branch lemmas, the CPU cap was hit (`1795398144158799928-3237619`; again for the
    separate step module, `1795398486996727629-3250001`).
  - Diagnosis with heartbeat caps (`1795398635675858127-3251513`) and a diagnostics probe
    (`1795398698429157343-3251976`): concrete-typed statements that apply `decodeEval` at projections drove
    `Nat.sqrt` / `Bool.decEq` unfolding.
    - Fix: generic helpers over an abstract domain (`callBind`, `contAt`, `stepAt`), the same shape as layer 1's
      `twoChildren`.
    - The probe module was archived to `drafts/opusA/UniformPolicyCompilerDiagProbe.lean.txt`, not left in the tree.
  - **PASS** `UniformPolicyCompilerStepProof` `1795398797920438628-3252959`.
  - **PASS** `UniformPolicyCompilerProof` `1795398807501890642-3253060`: `exactUniformCompiler : ExactUniformCompiler`,
    with axioms `[propext, Classical.choice, Quot.sound]`.
- Deliverables: `UNIFORM-POLICY-COMPILER-SOURCE-MAP.md` and `UNIFORM-POLICY-COMPILER-EVIDENCE.json`. Earlier drafts
  are in `drafts/opusA/`. A stray copy of the layer-1 v1 draft also sits at the `drafts/` top level; it is mine and
  was not deleted.

## Task: native realization on twins (P16)
- Read the gap map (§2, §3, §9), Opus B's ledger tail and twin tooling, the drafted `NativeOrdinalRealization{Targets,Proof}`
  and the handoff note.
- Copied the generator to `opusA/twin/make_twins.py`, adapted to skip any existing twin not in my own manifest, and ran it
  on the realization proof closure. Result: 536 modules, 534 legacy, **0 written**, 534 `skipped_existing`. All were
  already twinned by Opus B. `opusA/twin/TWIN-MANIFEST-REALIZATION.json` records that. No twin `.lean` was written by me.
- Re-checked Opus B's manifest for the closure: 534 twin and original shas match, and 8 bodies have the one-word
  `private` deletion.
- Verifying gates, both cache hits only:
  - `1795399532290638667-3260157`: the three `NativeClosed*Checks` twins, 532 modules, all rc 0.
  - `1795399550322108167-3260262`: the twin `NativeOrdinalRealizationProof`, 536 modules, all rc 0, peak 921,748 KiB.
  - First compile: Opus B's `1795399156663919873-3256109`. Axioms are standard for both theorems, and the drafted
    proof compiled with its body byte-identical.
- Root rescoped the task to reading deliverables only. Wrote `P16-LEM-REALIZATION-CORRESPONDENCE.md` and
  `P16-THM-ITERATION-CORRESPONDENCE.md`.
  - (a), (b), (c) are exact. (d) is exact under the abstraction-rule reading, which is all the printed proof and the
    later sections use. Under the literal reading (the general structural lemma) it is not comparable, and that
    lemma is also not stated in the paper.
  - `thm:iteration` is the printed theorem, named.
  - The 8 edited twin files lie outside both statements' definition closures.
