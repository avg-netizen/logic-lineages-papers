# Open literal count agreement on an actual supported needle

Exact gate `LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedChecks`,
alias `exact_OpenLiteralSupportedCount`.

The actual allCounts-one graph on [candidates,left,right], actual original
scratch membership of needle in candidates, and the two actual original
literal entryCount graph reports imply internal equality of the count
outputs. Arithmetic induction varies only the actual candidate tape,
holding the two original compare operands, needle and two actual count
outputs fixed. It opens the actual step in each cons; a head hit
transports the exact candidate slots, and tail membership uses the true
previous accumulator. This does not yet cover outside-support queries
or discharge TargetMemberLaw for the selected dCore.

Checked source identities:

f93129f589ed9715e1f41da9331d46e995f5594c47c3c2acdd8b2fa442130006  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalLiteralCountSupportedChecks.lean
808fdb18ad6b7e82686427008698ac155938cf886f1e79120b41a4c93bbab280  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalLiteralCountSupportedConsProof.lean
64c110a67ba0ef0eee693d0a7a3f62e7d1fc53e3a73bc2bc48b6901593dcea26  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalLiteralCountSupportedProof.lean
bcfbc0e7eaded86e52daf51ed7a5453bfe3f80ab45ee460f51d5588231c68c8b  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalLiteralCountSupportedSyntaxProof.lean
67ac7f12c82d0ee538672d637b37a719cad4696feaa468c61276be80414df8d2  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalLiteralCountSupportedTargets.lean
