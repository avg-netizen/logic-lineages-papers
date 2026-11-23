# Paper 16 `lem:realization`: finite chains of strict steps

The printed proof ends: "An induction on the number of beta steps permits any finite sequence." The
round-2 correspondence table (`../../local-fable-pair-2026-11-22-round2/opusA/P16-LEM-REALIZATION-CORRESPONDENCE.md`)
noted that this iteration of clause (a) had no Lean statement; later proofs iterate by hand.

Frozen `LogicLineages/NativeModule/PersistentMarking/NativeRealizationChainTargets.lean`
(sha256 `5a04283bd9360300fe1ea6a8a72157827122b5b0618fc7db2580df565ca1312d`), a module-system file on the
native copies:
- `RealizationChainBackward terms wf` — realization is transported backward along the transitive closure
  of the strict relation.
- `ExactChainOfStrict` — for every term structure, single-edge transport gives chain transport.
- `NativeRealizationFiniteChains` — on the closed native terms with their strict relation.

Proof: induction on the chain, from #1447's `exact_NativeRealizationClosure`.

With #1447's abstraction rule this formalises everything the printed proof of the lemma's last sentence
actually argues (abstraction rule, then finite beta sequences). It does not supply a structural
fundamental lemma over all typed native terms, and it does not settle the wording question the external
review left open; `lem:realization` stays pending.

## Lambda rule along finite chains (same round)

Frozen `LogicLineages/NativeModule/PersistentMarking/NativeLambdaChainTargets.lean`
(sha256 `9e30076f3954eec8d1b6d4b0ff2fc9b542d0db88bd4feea7e5a0040e953047bd`), `NativeLambdaChainRealization`:
if every closed substituted body instance of a closed native lambda realizes the corresponding value of
f, then every term that reaches that lambda through a finite nonempty chain of strict edges realizes f.
Proof: #1447's abstraction rule, then `exactChainOfStrict`. Receipt `1795402191005157732-3276200`.

## Wording proposal for the owner (not applied)

The printed lemma ends "The typed lambda fundamental lemma holds for these realizers", and both external
reviews keep the lemma pending because that sentence is broader than what is proved. The printed proof
argues exactly `NativeLambdaChainRealization`. A last sentence that says what is proved, and what the
later sections use, would be:

> For a closed lambda whose closed substituted body instances realize the values of $f$, the lambda
> realizes $f$, and so does every term reducing to it by finitely many strict steps.

With that sentence the lemma is the conjunction of #1447's `NativeRealizationClosure` and
`NativeLambdaChainRealization`, both compiled. Applying it is a manuscript change and the owner's call;
nothing has been edited.
