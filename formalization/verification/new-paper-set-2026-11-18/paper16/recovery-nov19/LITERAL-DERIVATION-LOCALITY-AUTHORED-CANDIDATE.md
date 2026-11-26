# Authored literal certificate and symbolic locality candidate

Pending independent authored review and a fresh exact gate. The original
15-pin target and all original source files remain unchanged.

- Soundness is an explicit fold on actual `Tree` constructors, using the
  corresponding original Prop rule at each node.
- Completeness uses all six original mutually inductive Prop recursors
  and sixteen explicit constructor builders. The builders retain actual
  rule data (endpoint terms, indices, owner tuple, all typed/fresh/
  precedence/split/removal guards), eliminate recursive Nonempty children
  only to produce another Nonempty, and do not use the auxiliary
  marked-target relation or Classical.choice.
- The actual given finite tree's root and all root/child footprint types
  are checked by direct data-tree induction. At literal selected owner
  indices, take the source universe projections with locally chosen
  complete finite inventories of the exact original owner; no such
  inventory remains in the public guard. Use its actual selected
  original argument type, subtype closure, original whole owner-argument
  table `ownerCopies`, and original `apply = some r` theorem to cover
  even copies that do not survive into r. Actual source/target opening
  uses the typed original singleton `openBody` substitution, and FAbs
  appends exactly that typed free variable. Multiset/list support
  projections follow the same literal occurrence witnesses; Whole retypes
  the same head and arguments to the actual supplied argument's root type.
- No change to existing checked semantics or source-window assumptions.
  Whole numeric locality still needs numeric rule/context/quotient facts
  for later paths. No positive simulation, ordinal or ID1 result claimed.

## Candidate source hashes
44acda52500da345bd46e34c62ce1580df19df1562b7769d938535edbf0ab684  LogicLineages/PersistentMarking/LiteralDerivationBuilderProof.lean
e47c6c86f3c9e68654e1198b018f67ac25223dd6eb700786c73f2e1e494fbd01  LogicLineages/PersistentMarking/LiteralDerivationCompleteProof.lean
b36efe1b14e8cdcf4382d51b518aecbcc24d18654c14d012f89166f0610fec26  LogicLineages/PersistentMarking/LiteralDerivationSoundProof.lean
cb0974fc243d4e0d8ba960d04f84f53d7ebe291d776c3c2a8075d2b3327f482f  LogicLineages/PersistentMarking/LiteralWindowSupportProof.lean
5d37e4e7081a682cc60f7c67ff61dc9176b8053f563ba3aa8217e97597958527  LogicLineages/PersistentMarking/LiteralWindowTermProof.lean
00c9dd21c4110c451f15ab7a6c5e10390ee2276dbfa302c16e474cbb9cbb8e4f  LogicLineages/PersistentMarking/LiteralWindowLocalityProof.lean
ca17316fadbcacb9d7d261a50925b139164f606afbd7ca1a100d1d1dc7c1d6d0  LogicLineages/PersistentMarking/LiteralDerivationLocalityChecks.lean
