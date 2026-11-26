# Independent current-tree reconciliation: acceptance001–012

Every acceptance evidence SHA resolves to its preserved report. All reported
local source hashes and actual output artifact hashes match the current tree
for all twelve records, including the list-shaped P16 evidence records. Explicit
acceptance source pins also match. Detailed per-record counts and empty drift
lists are saved in ACCEPTANCE-001-012-RECONCILIATION.json. This audit reads
sources/artifacts; it launches no native compiler and preserves original receipts.

The apparent shared StatementChecks growth is namespace growth, not source
replacement: original StatementChecks.lean still contains only modular/orbit
aliases; GrowthStatementChecks.lean and EffectivityStatementChecks.lean add
separate modules reopening that namespace. All three original exact-gate source
hashes still match their original evidence and current outputs.

Record010 full-control evidence includes the shared near-control definitions,
targets and mathematical proof suppliers (NearControlProof, NearGrowthProof,
EffectivityTargets/Proof) with matching current hashes and dependency evidence.
It does NOT include the three earlier exact-check modules or their aliases.
Thus010 is not a replacement audit of aliases002/005/006. Those remain valid
through their unchanged individually preserved exact-gate evidence;010 adds
new factorial/full-control aliases and reconciles their common proof suppliers.
No stale record is silently relabeled or original receipt erased.

P16 records001/003/007/011 likewise retain unchanged source and artifact hashes,
including shared Syntax/SpineSyntax and substitution/typing suppliers. New
free-covariance work resides in separate modules and is not implicitly accepted.
Historical limitations in early records describe what was pending then;
records010/011 explicitly add later results without altering old records.
No full-root build or CI result is claimed by this reconciliation.
