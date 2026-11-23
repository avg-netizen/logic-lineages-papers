# Opus B ledger, round 6 (23 Nov)

Task (Root): plan the internal proof of `lem:arithmetic-accessibility` (= `UniformAccessibility`) and prove the first
tractable non-accepted component(s). Rules: round-6 gate, no git, no rm, never edit existing .lean files.

- Plan: `opusB/ACCESSIBILITY-PLAN.md`. Induction rule found: `ID1Completion.InternalSliceInductionProof.actualInternalSliceInduction`
  with `InternalSliceInductionSyntaxProof.sliceReplacement` (ID₁ `inductiveLeastness`, one tag, invariant may mention the
  predicate negatively). C_τ already accepted (#578/#582). Chosen component: J closed under multiset union (premise-explicit).
- `ConditionalJUnionTargets` frozen: sha256 a5474b2bfd4e0e6cdaf9e99083e7069629342cdd267e425bc8f431b707f14f48, receipt
  `1795413375008112140-3314021`, 1,021,484 KiB.
- `ConditionalJUnionSyntaxProof` (templates `inner`, `outer`, `innerInv`, `edgeOuter`, `edgeInner`; subst/instance/relabel
  lemmas; `allOneRelabel`, `selfInstance`): first attempt failed on name resolution (`Term` → qualified), receipt
  `1795413492742802623-3314451`; PASSED receipt `1795413512780068926-3314580`, 1,111,424 KiB.
- `ConditionalJUnionProof.exact_ConditionalJUnion : ConditionalJUnion`: first attempt failed (a `rfl` needing both sides
  normalised; an implicit `body`), receipt in log r6_p; PASSED receipt `1795413770153441136-3315432`, 1,428 modules, proof
  module 1,108,620 KiB (gate peak 1,111,424). Axioms [propext, Quot.sound]; no sorryAx. Pure ID₁ derivation: two nested
  `actualInternalSliceInduction`s on the J slice, `actualOriginalAccessibilityIntroduction`, ∃-elimination twice, classical
  case analysis, equality elimination; premises only `CarrierUnion`, `MultisetSplit`.
- Root: J-union recorded as #1487. Next skeleton `ConditionalJSingleton`:
  `ConditionalJSingletonTargets` frozen: sha256 cec67446bf31e407ca50636ef18c67493fec0802f5016b38483027ae6691b867, receipt
  `1795414036638654354-3316320`, 1,019,860 KiB. `ConditionalJSingletonProof` first attempt failed (a rewrite also
  changed the hypothesis context in `nilJ`; uninferrable `cons _` placeholders); PASSED receipt
  `1795414175268303942-3316766`, 1,430 modules, 1,114,428 KiB. `exact_ConditionalJSingleton`, `exact_ConditionalJMembers`,
  axioms [propext, Quot.sound], no sorryAx.
- Design note `opusB/OPEN-TERM-ARITHMETIC-NOTE.md` (no proofs).
- Root: #1489 recorded; task: `NilNoStep` (then `NilCarrier`, `SingletonCarrier`) as theorems for the actual programs.
- **`NilNoStep` STOPPED (blocked)**, two independent reasons:
  1. The actual direct-replacement checker AST is not available. In the presentation `data i j r d`, `d : Program 3` is
     only known through `Evaluates` (it comes from `NumberedWindowConcreteCheckersProgramChecks.exact_AllFourProgramWitnesses`
     ← `NumberedWindowAddressCheckersProgramProof.certificates` ← `NumberedWindowDirectProgramChecks.exact_DirectCertificateProgram`,
     an `∃ p` from a Primrec proof). An open-term rejection fact about an AST known only extensionally is a true Π₁ sentence,
     not a derivable one; the internal proof must see the program.
  2. Even for a transparent AST of `NumberedWindowDirectAlgorithm.direct`, control flow at src = 0 on an open certificate is
     not shape-determined: `unpack 0 = some []` is closed, but `readWitness cert` runs `unpackNode` (case cert = 0 / succ),
     `decode` (bounded search `(candidates n).find?` with n open), `unpack` with the open code as fuel (`steps n`), and then
     the rejecting test is `decide ([].Perm (kept ++ removed)) && … && !removed.isEmpty`. The case analysis needed is:
     cert zero/succ; decode/unpack success or failure on open inputs (internal pair-decode laws exist: #1457
     `exact_OpenSuccess`/`exact_OpenFailure`); removed = nil (then `!isEmpty` fails) or cons (then `Perm [] (kept ++ h :: t)`
     fails, needing an internal law for the Perm-decision subprogram at an empty first list).
  Cheap alternative not taken (stop rule): install a transparent guard, d' := branch (src = 0) 0 d; `Evaluates` transfers
  because direct(0, _, _) = false; then `NilNoStep` needs only composition/projection elimination, the branch law and a
  numeral test. Usable because `UniformAccessibility` chooses its programs existentially.
- `NilCarrier` DONE without AST knowledge (closed instance): `ConditionalJNilCarrierTargets` frozen sha
  8ad148de70a6fb29f8c6079a4fe9ec1c51994e516cdefaf6ffc5cf1e45c8edb6 (receipt `1795414658276749382-3318614`, 1,030,988 KiB);
  `ConditionalJNilCarrierProof` PASSED after three small fixes (receipt `1795414761361050081-3319071`, 1,435 modules,
  1,093,092 KiB): `exact_ActualNilCarrier`, `exact_ActualJSingleton`, `exact_ActualJMembers`, axioms [propext,
  Classical.choice, Quot.sound], no sorryAx.
- `SingletonCarrier` not attempted: same two obstacles (opaque multiset-domain AST; `unpack` of the open singleton code
  `pack [q]` iterates with the open code as fuel).
- Root: NilCarrier recorded as #1492; guard route approved.
- `ConditionalJGuardTargets` frozen: sha256 4987b5076b1ee71de084fa4c3b12e7253bf16102517a09157eb79debb411ec3e, receipt
  `1795414972744542145-3319950`, 1,034,964 KiB. `ConditionalJGuardProof` first attempt failed (projection index under
  an unreduced `Fin.cases`); PASSED receipt `1795415061808575178-3320260`, 1,438 modules, proof module 1,099,296 KiB:
  `exact_GuardEvaluates`, `exact_GuardNilNoStep`, `exact_GuardedJSingleton`, `exact_GuardedJMembers`, axioms [propext,
  Classical.choice, Quot.sound], no sorryAx. All about `guardedDirect d`, not the original witness.
- `SingletonCarrier`: guard route judged feasible (visible tests with internal laws: #1457 sparse decode, sparse
  `fieldCons` laws), not built this turn. Design recommendation and dated table update in ACCESSIBILITY-PLAN.md.
