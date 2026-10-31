# Paper03 total-decision repair candidate

The full constructive mathematical repair is saved in PROOF.md, awaiting
separate review. It uses the independent Goubault-Larrecq--Schmitz2016
effective ideal decomposition for regular RANKED-tree languages, effective
Parikh conversion and Presburger arithmetic. NO Carter theorem is assumed.

The new bridges are complete:

1. The finite forbidden-graph profile gives a regular, downward binary
   parse language. Exact ranked leaf pruning makes each term ideal's
   graph image hereditary, and it is directed by the one-way embedding.
2. The finite graph-ideal cover has JEP iff one projected ideal equals
   the whole class. No reflection of binary-language JEP is used.
3. Each graph image has an explicit deterministic Presburger automaton
   on reduced cotrees. Subset-valued states and a child-subset-alphabet
   CFG account for ALL binary associations, permutations and repeated
   equal children. Parikh counts supply exact horizontal transitions.
4. Product/complement and finite productive-state saturation decide the
   inclusion tests. Empty classes and empty-only classes are handled.

The balanced/comb parses of four independent vertices are a required
countercontrol: their term language lacks JEP, but every maximal parse's
principal ideal projects to the whole graph class, so this algorithm
correctly answers YES. Source correspondence and new-effectivity claims
are separated from actual full-code implementation or Lean evidence.

Root owns the companion cotree semantics, bounded AC controls and canonical
manuscript edits. L3 ran no repair computation or Lean job. Public exports,
Git, the old native sweep and all other paused subjects remain outside scope.
Next exact step: complete root review of new bridges and independent source
alignment; repair actual diagnostics rather than assume acceptance.
