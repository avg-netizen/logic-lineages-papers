# Opus A ledger — round 5

## Task: effective cofinal family (thm:main item 6) + domain note
- Searched for an encoding of `Spine.Expr`. There is no `Encodable` or `Primcodable` instance. There is a `Nat` code,
  `NativeSyntaxCountabilityTargets.nativeCode = ((tr q).map encodeTerm).getD 0`, which is injective on closed native
  terms (#1448 closure). No `Primrec`/`Computable` facts exist for `tr` or `encodeTerm`.
- So effectiveness took this form: the explicit, computable (compiled, choice-free) Lean function
  `sequenceTerm : ℕ → Expr` (#1462), with its structural recursion equations as `rfl` theorems.
  - A `Computable (fun n => nativeCode (t n))` proof would need `Primrec` for `pair`, `encodeNode`, `encodeTy`,
    `encodeHead`, a total code function equal to `encodeTerm ∘ tr` on ordinary terms, and code recursions for
    `tierType`, `eraseBound`, the iterator, `binders`, `spine`, `natDown`, `towerB` and `downTerm`.
  - That is mechanical but large, and was not attempted.
- `ConditionalHeightEffectiveTargets` frozen: sha `441d25c6…e0d`, receipt `1795405209297027940-3293841`.
- `ConditionalHeightEffectiveProof` **PASS** `1795405228525235744-3293922`: `conditionalHeightEffective`, standard
  axioms, module RSS 945,288 KiB.
- `ConditionalMain16EffectiveTargets` frozen: sha `b6bf012c…fc5a`, receipt `1795405246789453837-3294054`.
- `ConditionalMain16EffectiveProof` **PASS** `1795405251540126890-3294118`: `exact_ConditionalMain16Effective`, standard
  axioms, peak 1,143,768 KiB (1,882 modules). It imports Opus B's proof; none of Opus B's files were edited.
- `HEIGHT-DOMAIN-NOTE.md`: the same domain. Printed `⊐` is defined "for ordinary terms of equal type"; the Lean
  `Domain` is exactly that.
