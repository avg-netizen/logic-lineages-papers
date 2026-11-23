# Height domain note (Opus A, round 5)

**Question.** `thm:height` (#1465) states the height over *ordinary* terms. Is that the printed domain of `⊐`?

## Printed definitions
- `paper.tex` l. 32: `\newcommand{\cs}{\succ_c}`.
- `ordering.tex` l. 206–212, Definition `def:confined` (Confined pair):
  > For ordinary terms of equal type define
  > s ⪰_c t ⟺ W s t ∧ Ty(t) ⊆ Ty(s),  s ≻_c t ⟺ St s t ∧ Ty(t) ⊆ Ty(s).
- `foundations.tex` l. 13–19:
  > An ordinary term is a well-typed finite expression formed from variables, abstraction, application, and the
  > constants 0, S, D^τ, R^τ
- `ordinals.tex` l. 22: ranked heads belong to the fixed finite signature.
- `thm:upper` (l. 316–317): "rk_⊐(s) < BH for every ordinary term s".
- `thm:height` proof: "Taking the supremum of ranks plus one gives equality".

So `⊐` relates only ordinary terms of equal type, and its field is the ordinary terms of the signature. Marked comparison
terms occur only inside proofs of `St`/`W`; they are not elements of `⊐`. The printed height is the supremum of rank + 1
over that field.

## Lean definitions
- `ConfinedPair.Strict S s t := Domain S s t ∧ Spine.Strict S s t ∧ Included t s`.
- `ConfinedPair.Domain S s t := ∃ τ, PaperTerm S s τ ∧ PaperTerm S t τ ∧ Ordinary s ∧ Ordinary t`.
- `PaperTerm S q τ := Typed EmptyContext q τ ∧ Valid S q`: well typed, no loose de Bruijn index, free names allowed, ranked
  heads in the signature.
- `Ordinary` is false exactly on `.marked` heads.
- `ConditionalHeightTargets.OrdinaryTerm S := {q : Expr // ∃ τ, PaperTerm S q τ ∧ Ordinary q}`.
- `descendingHeight S wf := ⨆ q : OrdinaryTerm S, succ (confinedRank (wf.apply q.val))`.

## Verdict: **the same domain**
- The Lean `descendingHeight` ranges over exactly the field of the Lean `⊐`: `Domain` admits precisely the
  `PaperTerm ∧ Ordinary` expressions of a common type. That field is the printed one, "ordinary terms of equal type".
- The rank is taken in the same relation, the full confined strict relation on `Expr`.
- An `Expr` outside `OrdinaryTerm` has no `⊐`-edges at all, in either direction, so it is not in the printed relation.
  As an element of `Expr` it has rank 0, which would contribute only `1 ≤ BH` to a supremum taken over all of `Expr`.
- My round-4 reading note ("if ⊐ ranged over marked terms…") is therefore settled. It does not; no wider statement is
  needed and none was proved.
