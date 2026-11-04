# Finite ground-context tower prerequisite

Source paper06 lines582–597,620–622: explicit context bookkeeping prerequisite for later restricted nested ground-lambda substitution. This component states no nested-lambda theorem.

The actual typed groundContext recursion prepends ground k times. GroundContextEquation identifies its exact list order with replicate k ground ++ Gamma. GroundRenaming is an actual typed variable map, identity at zero and there composed with the previous map at successor. GroundRenamingEquations gives literal term identity and the exact successor equality to one further weakening, for arbitrary term types and constructors; it is syntax only.

GroundTowerComputability fixes a finite height k and supplies one positive scalar body at each natural index, requiring calibration only for j<=k against the matching actual groundContext j Gamma. The same successful decoded Context, SubtypeClosed and original literal ground-term confinement are explicit. Its conclusion is an iff between ground C at the original representative and ground C at its k-fold weakened representative; no numeric code identity is asserted. At k=0 the result is literal identity, although its calibration premise remains explicit.

Proof correspondence: induction on k, restrict the supplied finite calibration family for the induction hypothesis, derive confinement of the k-fold rename by actualRenaming, use accepted one-step ground C equivalence with scalar k/scalar(k+1), and rewrite the successor renaming equation. This derives transport of arbitrary computable ground arguments without assuming general C weakening. No higher-type semantic transport, tower uniform encoding/PR claim, nested-fragment theorem, ID1 derivation or global WF. Proof absent until review/freeze; no export.
