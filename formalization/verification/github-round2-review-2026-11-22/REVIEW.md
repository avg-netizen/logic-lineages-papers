# Round-2 source review — 22 November 2026

**Reviewed commit:** `1cd1734feb2b64c5a9936b2b5e8649f9b2f3889c` on
`formalization/github-measured-install-2026-11-22`, relative to
`a14a936772e01363795c919c106607fdad368f8c`.

**Outcome:** no material defect was found in the new Lean propositions or their
claimed supporting scope. Paper 17's strengthened comparator closes the earlier
supplied-policy and joint-near-control uniformity gaps. Paper 16's iteration
statement matches the printed countable-ordinal setting. The broader lambda
fundamental-lemma sentence remains outside the proved abstraction rule.

This review corrects assumption summaries, restores exact historical evidence
documents, and updates the handoff. It introduces no Lean source change or
numbered promotion. The register remains **159 checked / 8 pending / 167**.

## Findings and corrections

### R1 — clarify the installed application's type-checker premise

**Low severity; documentation corrected.** The round-2 handoff compressed the
input assumptions to two accepted operand addresses and two type guards. The
general output-address, frontend-acceptance and continuation-functionality targets
also require matching operand address reports at one shared context and acceptance
of the codomain by the scalar's arbitrary type program `tv`.

For the `tv := TV` specializations, the original syntax guard supplies that last
check. The general `tv` version must retain `unary tv (suc z) cod`: acceptance of
the function's arrow type and the argument's domain does not supply acceptance of
the codomain by an arbitrary program. The targets and accepted-record scopes
already say this correctly. The mutable handoff summary is corrected; the frozen
opening paragraph of `fable2/OUTPUT-ADDRESS-SOURCE-MAP.md` is qualified by this
review without changing its pinned bytes.

### R2 — distinguish the uses of the original guards

**Low severity; frozen-map erratum recorded.** The paragraph in
`fable2/OUTPUT-FUNCTIONALITY-SOURCE-MAP.md` saying the original two guards and the
additional result check are used only for output scalar acceptance is too broad.
The original syntax/refit guards also supply application-window formation and
application least existence. Only the additional arbitrary-`tv` codomain check is
specific to output scalar acceptance. The standalone functionality theorem, which
holds the application's least as a premise, requires neither category of guard.

The detailed evidence and corrected wording for R1 and R2 are in
[P16-APPLICATION-REVIEW.md](P16-APPLICATION-REVIEW.md). All three packets preserve
the same installed exchange/window/least/scalar/application route. Their output
and continuation claims are correctly limited; no false operand congruence or
internally universally quantified functionality claim is added.

### R3 — preserve the historical versions named by evidence

**Low severity; provenance repaired.** Five native evidence files retain hashes
of earlier versions of two documents: the uniform-main source map (#1437, #1439,
#1445), and the initial module-copy manifest (#1446, #1447). The final acceptance
records explicitly refresh their outer pins after those documents grow, but the
older bytes were absent from the published checkpoint.

The original source-map prefix, the initial 653-copy manifest and its generator
have now been recovered deterministically from the published contents. Every
recovered snapshot exactly matches its previously recorded SHA-256. They are
stored under `historical/`; [PROVENANCE-RECONCILIATION.json](PROVENANCE-RECONCILIATION.json)
maps each historical path and hash to its snapshot. No historical evidence,
acceptance record, or frozen Lean source has been rewritten.

The final copy inventory is **671 generated copies plus one new rank assembly
module**. Of the 671 bodies, 661 are byte-identical, eight files contain nine
`private`-modifier removals in total, and two files contain recorded proof-term
repairs. The earlier phrase "eight one-word private deletions" in the initial
copy source map and #1446 scope should be read as eight affected files; one of
those files contains two modifier removals. The current handoff now gives the
exact count. Import redirection and every recorded body change match the manifest.

### R4 — replace stale publication and review status

**Low severity; current documentation corrected.** The published round-2 handoff
still described its files as untracked and the round as uncommitted. It also left
the source-comparison read as future work. Its current status now identifies the
reviewed publication and the completed source assessment. Creation-time ledgers,
source maps and accepted-record scope descriptions remain historical evidence.

## Mathematical conclusions

| Packet or statement | Review conclusion | Remaining boundary |
| --- | --- | --- |
| Paper 17 `UniformMainComparison`, #1445 | The supplied policy code is a runtime argument of one partial-recursive evaluator; the near-control parameter is also a runtime argument. The compiler and decision assembly preserve valid-program termination and rejection. The literal hardness reductions have the required direction and are independent of policy/control. | The existing formal interpretation of control laws, canonical assignments and original-domain circuit semantics is retained. Numbered promotion is a separate register decision. |
| Paper 16 application packets, #1438/#1440/#1442 | Construct an accepted output address, prove acceptance by the actual application graph, and identify every accepted output with that address under the stated hypotheses. | The original type guards remain. Arbitrary `tv` needs the extra codomain check; continuation scope is explicit. |
| Paper 16 corrected structural interpretation, #1443/#1449 | The fixed-point qualification is now present where full application needs it. The interpretation and substitution conjuncts match the corrected finite typed setting. | The previously identified bottom-family counterexample remains relevant and is preserved. |
| Paper 16 iteration, #1446 | Matches the printed finite-type, arbitrary-function, countable-ordinal and full-prefix convention-(I) scope on the retained native copies. | Ready for a numbered promotion decision; this review does not change the register. |
| Paper 16 realization, #1447 | Matches backward transport, downward closure and nonempty countable pointwise suprema; also proves the one-binder abstraction rule. | The printed full "typed lambda fundamental lemma" sentence is broader than the abstraction rule. Keep the numbered lemma pending until that theorem is supplied or its intended wording is settled. |
| Paper 16 rank packet, #1448 | Supplies the recorded native rank laws, countability, restriction comparison and unconditional closed-native-rank assembly. | It does not supply rank-equals-ID1-norm, the internal accessibility proof, or the external norm/height theorems. |

Detailed source comparisons:

- [P17-UNIFORMITY-REVIEW.md](P17-UNIFORMITY-REVIEW.md).
- [P16-SOURCE-REVIEW.md](P16-SOURCE-REVIEW.md).
- [P16-APPLICATION-REVIEW.md](P16-APPLICATION-REVIEW.md).

The structural-interpretation verdict concerns the corrected TeX source and its
checksum. The round's existing record explicitly says that `paper.pdf` was not
rebuilt; this review does not treat that PDF as the corrected manuscript.

## Verification performed

[CHECKS.json](CHECKS.json) records the source/provenance checks. The reviewed
commit adds 700 Lean modules and changes no pre-existing Lean file. The pinned
compiler, dependency manifest, gate script and project instructions match the
preceding checkpoint.

All current Lean pins in the twelve new supporting evidence records match their
files. The 24 recorded endpoint axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. The recorded consolidated gate covers every
one of the 700 new roots in a 6,546-module closure: 6,297 verified cache hits and
249 compilations. That log prints axiom output for compiled modules; cached
endpoint reports are retained separately in the per-record evidence JSON.

The original full JSON receipts remain on the authoring host. This review
checks the published evidence summaries, source identity and log coverage; it
does not assert fresh access to those receipt bytes or a second native run.
The existing Lean gates remain the proof-validity evidence. Source correspondence
and copy-body comparison are separate from that validity claim.

The local native queue remains paused. Publication of this completed review and
its documentation/provenance corrections is explicitly authorized in
[RELEASE.md](RELEASE.md).
