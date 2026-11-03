# The unrestricted marked-source transitivity candidate is not accepted

The new `SourceFinalTransitivityTargets.ActualUnmarkedFinalComposition` was
compiled/frozen, but has **not** been proved or accepted. Its arbitrary marked
source domain is too large for the immutable literal partial `strictMark`.
Do not promote or import it as a proved supplier. The following exact finite
counterexample is now FULLY CHECKED by the three frozen gate aliases in
`MarkedSourceTransitivityCounterexampleStatementChecks`, receipt
`1793665307930623465-2`, using only `propext` and `Quot.sound`.

Take ranked symbols `F > K > Z`, arities 1, 1, 0, and all terms ground/closed.
Write `k = K(Z)` and `q = K*(k)`. Define

```
S = F*(q)       T = F*(k)       U = F(Z).
```

The actual extended `In` rule yields `S Weak T`, since `q Weak k` by zero-tuple
Select followed by ordinary reflexivity. Actual `Stat` yields `T Weak U`:
`k Strict Z` by positive marking and zero-tuple Select, and the whole `T Weak Z`
side premise is another zero-tuple Select followed by `k Weak Z`. The final
`U` is fully Unmarked.

In contrast, actual ORIGINAL `S Weak U` has no derivation. `Copy` would require
`F > F`. `Stat` on the singleton base would require `q Strict Z`, but literal
`strictMark q` is `none`. `Select` can only select `q`, with an empty tuple
because its type is ground. It would require `q Weak F(Z)`. Successive source
root inversions reduce that to `K(Z) Weak F(Z)`, then `K*(Z) Weak F(Z)`, then
`Z Weak F(Z)`, then `Z* Weak F(Z)`; each Copy/Stat head guard fails, and the last
marked constant has no selectable argument. None of Var/Abs/Fun/Put/F-Abs
supplies a further case at the relevant marked ground source/ordinary target.

This does **not** refute the confined pair's transitivity: its original source
is an ordinary embedding, and `S` here has a marked base argument. Future exact
transitivity targets must preserve the actual ordinary-source/origin domain.
The frozen overly broad candidate must remain visibly unaccepted rather than
being silently weakened. All previously accepted elimination, substitution,
marking, target-dropping and literal application-composition gates are unchanged.

This is a diagnosis of **our explicit typed auxiliary presentation and proposed
generalization**. It is not a claim that Kop's published transitivity theorem
is false. No full correspondence with that theorem's entire marked domain was
proved. In particular, the immutable local `Strict` uses partial `strictMark`.
The separate original-only endpoint-transitivity candidate in
`SourceFinalTransitivityTargets` has not been refuted by this example: its
first premise would require ORIGINAL `S Weak T`, whereas the exhibited first
step uses auxiliary `In`. Keep those two propositions distinct.

`OrdinaryTransitivityTargets` records the exact three-ordinary-embedding weak
transitivity and both mixed-compatibility obligations. It is a NEW explicit
source-domain target, not a silent edit to the frozen overly broad comparator.
