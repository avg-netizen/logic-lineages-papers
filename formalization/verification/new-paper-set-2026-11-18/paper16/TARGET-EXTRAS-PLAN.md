# Target extras source scope and route

Source: composition.tex, lem:target-macros, lines 457–491. Three full assertions: suffix deletion, occurrence-preserving permutation, and appending a finite list of original-target prefix copies. Targets are arbitrary marked owners; sources may contain arbitrary marks. No ordinary-target assumption, cut, comparison composition, or output-validity premise. Typing/validity of all transformed owners must follow from the input comparison and the literal list witnesses.

Freeze `TargetExtrasTargets.FullTargetExtras` as the conjunction of all three exact assertions. Existing `Permutation`, `PrefixCopies` and original `ExtendedTree` remain unchanged.

Proof plan: induct on actual E witness count; retain each root continuation. Only In/Marked1/Marked2 can create the marked target. For In suffix deletion, split actual ordered pairing to recover a corresponding source suffix; reconstruct In on prefixes, then Drop restores source suffix. For permutation, remove source occurrences in lockstep with target Remove witnesses and reconstruct actual inverse source permutation. For copies, each original target prefix has a corresponding source prefix by actual ordered pairing; construct source-prefix-to-target-prefix In witnesses, append these pairs, then Copies removes the source copies. The base matching is unchanged. Marked1/2 restrict/reorder target Whole witnesses; copies use the same root with restricted Whole target prefix witnesses, at each requested annotation, and append these genuine whole-source comparisons.

Retaining roots Put, Select/PSelect, Drop/Perm/Copies reuse their original source premises and lift smaller target transformations. Binder/free/head target rules are excluded by constructor equality, not an Ordinary assumption. Every recursive continuation is an actual smaller tree; no arbitrary derived comparison is recursively fed to the induction. All occurrence-level source recovery and new target typing must be paid internally.

This is independent scope planning only; no proof/native acceptance yet. Application covariance full gate remains separately pending.
