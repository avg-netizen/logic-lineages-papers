# Opus A ledger — round 3

## Task: B_l for every l (native tower realization)

Plan (written before any Lean):
1. Printed claim (ordinals.tex 531–550). `A_0=ι`, `A_{l+1}=A_l→A_l`, and `B_l h h_l⋯h_1 = Fix(λα. h^α h_l⋯h_1 0)`
   at type `A_{l+2}`. The native realizer is `λh:|A_{l+1}|.λh_l:|A_l|⋯λh_1:|A_1|. fix (λα:σ. (It_{A_l} α h h_l) h_{l-1}⋯h_1 Z)`;
   for `l=0` the body is `It_ι α h Z`. "use fix for Fix".
2. Semantic side. The value realized is `Bsem φ l`, with `h^α x := orbit A_l h x α` (convention (I)) and `0` = zero.
   `Fix` is taken to be the value `φ` realized by the fix term. The printed fix (line 527) has `φ f z = f^ω(z+1)`;
   that is Opus B's arithmetic layer, and its `OmegaArithmeticEquations.fix` is the same equation. So I quantify over
   any closed native `F ⊨ φ`. No Simmons, ψ_B or BH notion is defined.
3. Syntax module. An environment-indexed spine: slot `j` (1..l+1) holds `bound j` or a closed term, and `α` is
   `bound 0` or closed. Lemmas:
   - substitution distributes structurally over the spine and the binder prefix;
   - closed subterms are unchanged (`ClosedSyntaxProof.term`);
   - a slot at the substitution depth becomes the closed argument (`closedShift`);
   - typing of every partial tower (`NativeIn` helpers re-derived, `ClosingProof.weakening`,
     `exact_ClosedNativeIterator`).
4. Induction. Downward on the number `k` of remaining binders, from `k=l+1` (the printed term) to `0`. Claim(k): if
   slots `≤k` are bound and slots `>k` are closed realizers of `xs j`, then the partial term realizes
   `curryEnv k G xs`.
5. Step `k+1→k`: apply `exact_NativeLambdaRealization`. Its substituted body is the beta result
   `exact_ClosedNativeBeta`, and the syntax lemma identifies it with the partial term at `k`, at an updated
   environment.
6. Base `k=0`: the term is `app F (λα.Sp)`, and `F ⊨ φ` gives application by definition. `λα.Sp ⊨ (α ↦ spine value)`
   comes from the abstraction rule again; the substituted spine is the closed `It_{A_l} i P U` spine.
7. Spine:
   - `exact_NativeIteratorRealizesFullPrefix`, whose witness equals `orbit` by `exact_FullPrefixOrbitExists` uniqueness;
   - then arrow realization (definitional application) for each `h_{j}`;
   - finally `Z ⊨ 0`, since `0 ≤` any rank.
8. Strict backward transport along beta edges enters only inside `exact_NativeLambdaRealization`; no new edge facts
   are needed.
9. Modules, all under `LogicLineages/NativeModule/PersistentMarking/`: `NativeTowerTargets` (frozen),
   `NativeTowerSyntaxProof`, `NativeTowerProof`.
10. Coverage: realization of every `B_l` given `F ⊨ φ`. With Opus B's `LiteralNativeArithmeticRealizes`, this is the
   printed `B_l` for every `l`. It is not (D)'s identification `Δ_n=ψ_B(a_n)`, not (R), not `thm:height`: those
   need the external calibration.

Execution:
- Targets frozen. `NativeTowerTargets` sha `a4f51a00…2aec`, compiled alone with receipt `1795402383492741785-3277208`.
  - It took four earlier compile failures, all inside `zeroValue` / `spineValue`: noncomputable `orbit`, then
    lemma-name drift for ordinal zero (`not_lt_zero`). Receipts `…2344100703784-3276921`, `…2352206930907-3276986`,
    `…2361377337504-3277054`, `…2369124830569-3277117`.
- `NativeTowerSyntaxProof` **PASS** `1795402486217973933-3277777`. One earlier fail (`…2467673575924-3277651`): a
  missing `open`, and a `rw` replaced by a defeq `exact`.
- `NativeTowerProof` **PASS** `1795402619861101760-3278384`: `exact_NativeTowerRealization`, standard axioms, peak
  945,812 KiB.
  - One earlier fail (`…2608956526406-3278341`) came from two unqualified theorem names.
  - The proof itself elaborated as written the first time.
- Opus B's `exact_LiteralNativeArithmeticRealizes` twin compiled (rc 0, receipt `1795402092285333664-3275481`, in the
  #1456 closure), so I added the printed instance:
  - `NativeTowerPrintedTargets` frozen (sha `a7d91a50…c2df`, receipt `1795402698832557428-3278827`).
  - `NativeTowerPrintedProof` **PASS** `1795402711003426157-3278878`: `exact_PrintedTowerRealization`, standard axioms.
- Evidence: `NATIVE-TOWER-SOURCE-MAP.md` and `NATIVE-TOWER-EVIDENCE.json`. No twin was generated and no tracked file
  was edited.

## Task: (D) tower sequence t_n
- Plan: `t_n` built literally from #1459's `B_l`, `ordinalNext` and `omegaCarrier`. `Δ_n'` is the semantic composite.
  The proof is application by definition, plus induction on `l` for the spine `B_l B_{l-1}⋯B_0`. `a_n` enters only
  the interpretation, never the term, so nothing external is needed.
- `NativeTowerSequenceTargets` frozen: sha `830ba166…b754`, compiled alone, receipt `1795402872232949190-3279494`.
- `NativeTowerSequenceProof` **PASS** on the first gate, `1795402918597835057-3279644`:
  `exact_NativeTowerSequenceRealization`, standard axioms, module peak 941,296 KiB. `rfl` checks were added for
  `t_0` to `t_3` and for `Δ_0'`, `Δ_3'`.
- Wrote `NATIVE-TOWER-SEQUENCE-SOURCE-MAP.md`, with the `thm:height` step table and the external residue E1–E4, and
  `NATIVE-TOWER-SEQUENCE-EVIDENCE.json`.
