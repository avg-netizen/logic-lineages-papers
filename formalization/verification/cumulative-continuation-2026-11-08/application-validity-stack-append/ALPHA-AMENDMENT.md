# Binder-only specification amendment

Native preflight rejected `prefix`, a reserved Lean keyword, as a bound
object-term variable in the original append targets. Before proof authoring,
the two binders and their four bound references were renamed to `frontWork`.
Independent review accepted that exact amendment, and amended preflight passed.

Affected source:
`LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/InternalApplicationValidityStackAppendTargets.lean`

- Original SHA-256: `61eb4964dae2848496c3aa33c061b51e93629224fc53ab438ba761283eb142bb`
- Amended SHA-256: `7c63c844cb2978033d34fcacda42601ee76e296dd2f25df81fb010026d944976`

Replacing the six new `frontWork` identifiers by `prefix` recovers the
original source bytes exactly. No comments, quantifier domains, premises,
conclusions, ASTs, definitions, correspondence, or preflight comparator
aliases changed. The original failed source and evidence remain preserved
locally; they are not part of this public packet.

`PUBLIC-FROZEN-SOURCE-PINS.json` retains the exact reviewed source and supplier
hashes and this amendment history without local runner information. The full
original freeze and amendment manifests remain preserved locally. The initial
freeze correspondence describes its then-pending validation; `ACCEPTANCE.json`
and `STATUS.md` record the subsequent checked result.
