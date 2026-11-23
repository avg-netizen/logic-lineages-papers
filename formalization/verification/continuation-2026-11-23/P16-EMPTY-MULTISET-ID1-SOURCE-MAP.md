# Paper 16: empty multiset in the original internal J

Manuscript: `16-persistent-marking-termination-ordering/sections/ordinals.tex`,
lines 84–98 (the tagged I/J operator and strict finite occurrence replacement)
and 142–153 (internal multiset closure). This proves the empty base only.

From original #571 evaluation witnesses, keep i, j and r literally and choose
the direct checker with an explicit source-zero branch. Numerically this is
still the actual original direct checker: zero is the packed empty list and
a literal partition of it cannot remove a nonempty list. The test leaves every
other input's direct result unchanged. Interpret and instantiate the original
rules freshly at the chosen body. This does not replace d in an existing #660
installation or transport any open formula between numerically equal programs.

For an arbitrary open successor and arbitrary open certificate witness, use
the selected checker AST's projection and zero branch to make an internal
graph proof of output zero. Internal uniqueness refutes accepting output one.
Eliminate the exact existential certificate in the original odd edge, then
derive the universal successor premise. The closed numeral graph is used only
for the unchanged J carrier program at numeral zero. Original introduction
gives J(0) on that same selected body. There is no assumed edge absence, no
inference from standard-model truth, no J union or nonempty multiset result,
and no universal scalar all-terms derivation.

Native candidate (pending):
`LogicLineages.PersistentMarking.NumberedWindowInternalEmptyMultisetChecks`.
Exact authored source SHA-256:
- a6a9903335e302153c18def1d6600661e3e7a3d424f442adaad3d4353a0e2b8f  LogicLineages/PersistentMarking/NumberedWindowInternalEmptyMultisetChecks.lean
- 9d829d1090a1f71eff52c3085a3ada0e21b460764f4c371986cf4ff0019e6a1f  LogicLineages/PersistentMarking/NumberedWindowInternalEmptyMultisetProof.lean
- 1563d4883ee22f40a5efa3b89d504c1fe2cae07353cded8804cdc95a74b152fa  LogicLineages/PersistentMarking/NumberedWindowInternalEmptyMultisetTargets.lean
