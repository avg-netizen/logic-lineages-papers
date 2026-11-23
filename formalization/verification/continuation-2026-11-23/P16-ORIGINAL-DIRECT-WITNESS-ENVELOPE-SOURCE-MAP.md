# Paper 16: literal direct-multiset witness envelope

Source: `16-persistent-marking-termination-ordering/sections/ordinals.tex`
lines 74–76, 84–98 and 142–153. This packet is an exact parser/graph
front end, not acceptance of a direct certificate or closure of J.

The selected tag-5 witness check and selectors literally read kept,
removed and inserted raw tapes in that order. The same exact three-field
selectors with tag 4 read every insertion's target, dominator and supplied
certificate, in that order. The original sparse field parser, whose explicit
nil/cons recurrence handles the actual ordered packed lists, runs on the
three supplied raw tapes. The numerical equality is against original
`NumberedWindowDirectAlgorithm.readWitness` on all inputs, including malformed
lists/tags, preserving duplicates, order and the original certificate.

For arbitrary free object terms, each selected three-field guard plus its
actual selector graphs is equivalent in the original object calculus to
literal packed equality with those same terms. This uses checked sparse
cell/arity reports and their original open inversion, not semantic reflection.
We do not yet open arbitrary list or multiset witness acceptance for the
original d, impose perm/removed/insertion checks, assemble a replacement d,
or derive any J membership. Existing selected bodies are unchanged.

Native candidate (pending):
`LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelopeChecks`.

Exact authored source SHA-256:
- ef5789e57aec9a3e8c6fae11151f8640354526894f8a3177b13350862be9c41b  LogicLineages/PersistentMarking/NumberedWindowInternalDirectWitnessEnvelopeChecks.lean
- 4893e04e416d8be00402fd6377ac579bec0d3686d74a8dd81b7be58d6308bc11  LogicLineages/PersistentMarking/NumberedWindowInternalDirectWitnessEnvelopeNumericProof.lean
- 96d87ee4812dd7e33383f8dab6f777145a6404404854f573997db6cc854b1955  LogicLineages/PersistentMarking/NumberedWindowInternalDirectWitnessEnvelopeOpenProof.lean
- 3fa5417e857b7500905acd2987f6b939d70e3ce08519ef864e5ab72d4d03f637  LogicLineages/PersistentMarking/NumberedWindowInternalDirectWitnessEnvelopeTargets.lean
