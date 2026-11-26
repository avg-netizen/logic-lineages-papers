# Paper16 source and recovered owner-receipt audit

Scope only; this is neither a new native success nor an acceptance record.
The recovered owner machine's READY receipts precede the cloud recheck.
All seven packets' recorded source pins and recursive module source hashes
match the current source checkout; shared modules agree byte-for-byte.
Their combined closure is 527 modules. The absolute object/receipt paths
in the owner evidence identify a different machine, not local cloud objects.

## Structural application is not an arbitrary-stage equality

In `sections/decision.tex` (the structural interpretation subsection),
the interpretation is initially specified at a constructor family `M`. The
lemma then says the helper interprets concrete substituted full application,
including its undefined cases. A literal equality of the whole values at
that same `M` is false even for the identity substitution, a successful
typed call and a valid environment. Packet 396 checks that at the bottom
family, the ordinary successor applied in one full call to the covered
ground free variable succeeds syntactically and returns a retyped marked
successor; the helper consults the prior constructor family, hence has
availability false, whereas interpreting that marked result builds the
current constructor, whose availability is true. Thus the two codes differ.
No failed application, partial currying, weakening of the scope or forward
reference to fixedness is responsible for the difference.

Packet 398 checks the corresponding genuine full-application equality
(including the undefined whole-bottom case) when the constructor family
is a fixed point. This is a different, supporting contract and does not
discharge the numbered arbitrary-family lemma. A stage shift would need its
own exact statement because arguments and residual terms can themselves
depend on the family; no generic one-stage shift is established here.

The adequate soundness argument does not use the false equality. It retains
a hereditary *relation* at each finite stage and proves directly that the
actual scoped interpreter and whole helper relate to the actual original
bound substitution/application. Completeness uses the genuine fixed-point
application theorem and original derivation induction. Thus the numbered
adequacy proposition is separate from the overstrong structural assertion
cited in the source proof.

## Recovered queued scopes

| Packet | Literal comparator scope | Owner receipt |
| --- | --- | --- |
| Completeness, supporting | Both original finite judgments imply the corresponding least-fixed-point bits under exactly the source/observation guards; separate strict-field/mark law through initial lambdas. | `1795036823200258689-144`, 303 modules |
| Sound relation, supporting | Hereditary relation over valid extension contexts and actual original whole calls, including literal bottom for undefined results. Bottom, downward closure, and restriction only. | `1795036911869441700-16`, 119 modules |
| Sound stage, supporting | Original stage and all finite bottom iterations preserve the hereditary relation on positional base values and extra occurrences. No standalone observation converse claimed. | `1795037625891233452-14`, 286 modules |
| `thm:adequacy` | Both iff directions, actual least fixed point, every permitted source and observation at each valid context, same typed endpoints. | `1795038434615341512-12`, 339 modules |
| `thm:decide` | Executable Boolean tests for weak, strict, and both confined judgments; all ordinary typed pairs, including unequal annotation types. Uses finite literal support for confinement and an actual finite stage computation. | `1795038575414388282-13`, 344 modules |
| `thm:rpo` | Ground typed ranked fragment with ground variables; literal multiset occurrence witnesses, target-argument domination, and recursive multiset equality. A signature's admitted ranked heads have unique rank positions, so its equivalence on the fragment is head identity. | `1795039135337979246-17`, 79 modules |
| `lem:carrier` | Literal zero-recursion native term at any actual base type, closed P,K,U, original marked owners and one-/two-/three-copy whole Select prefixes. First strict comparison and the implication for every support-guarded closed ordinary target, with no native restriction on that target. | `1795039354222837109-12`, 225 modules |

`lem:indexed-carrier` has an owner-frozen literal comparator with 11 matching
pins; target preflight succeeded on the owner host. Owner typing/context
drafts were preserved; the new selector/check leaves are separate unchecked
drafts until a new exact gate and independent source review.
