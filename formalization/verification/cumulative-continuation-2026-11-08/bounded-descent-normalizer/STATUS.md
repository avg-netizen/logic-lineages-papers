# Generic bounded-descent normalizer: exact gate passed

Six supporting targets are checked at their unchanged frozen types:

1. The explicit transition fixes zero for every pair of arbitrary unary leaves.
2. If value <= fuel and the original numeric repeat graph returns out after
   fuel iterations from value, the actual transition graph T(out,out) holds.
   This includes fuel zero.
3. The normalizer's output is at most its original input.
4. Every normalizer output satisfies the actual transition graph T(out,out).
5. Exact-one input validity implies exact-one output validity.
6. The original left-selector graph at an arbitrary symbolic tag is preserved.

The literal original AST computes r=R(x), accepts r only when r<x,
V(r)=1 and the original left tags agree, and otherwise returns x. The
normalizer B uses the existing numeric repeat program for exactly x+1
iterations from x. Both leaves, positive bodies, derivation contexts and
symbolic arithmetic terms are unrestricted. No calibration, preservation,
termination, canonicality or fixed-point premise was added.

## Internal argument

The exact-one conjunction and original conditional equations give a
strict-or-equal transition split, validity preservation and left-tag
preservation. The impossible strict-below-zero branch yields T(0)=0.

One full-language induction in the unchanged InternalCalculus simultaneously
proves the output bound, both preservation implications and the stronger
fuel conclusion. Input, output and tag are universally quantified inside the
invariant, so it applies to the actual next transition value. The successor
case uses the original front-successor iteration law. A stationary first
step uses the already checked fixed-point iteration theorem; a descending
step decreases the symbolic bound from successor fuel to fuel. The zero case
combines zero-repeat equality, value <= 0 and the proved T(0)=0 graph.

All six public results then specialize the literal normalizer composition.
The fixed-point conclusion is T(out)=out, not B(out)=out or R(out)=out.
No standard-model truth-to-derivability reflection is used.

## Acceptance and provenance

Independent specification review accepted the frozen contract before native
preflight and proof authorship. All five frozen-file pins and 37 selected
original-source pins remain unchanged. The initial FROZEN-SPECIFICATION and
SOURCE-CORRESPONDENCE are retained as the pre-proof snapshot.

The six exact comparator aliases pass, and their actual axiom closures contain
only propext, Classical.choice and Quot.sound. Own-module namespace audits
cover 65 theorem declarations: 19 syntax, 6 support, 7 step support, 12 step,
9 induction, 6 public results and 6 exact aliases. Imported namespaces are
not used as a substitute for their own-module audits.

All 1,066 modules in the focused local import closure, including meta imports,
have successful immutable receipts matching their current source hashes.
CLOSURE-SOURCE-PINS.json records that full closure separately from the frozen
selected SOURCE-PINS.json. Receipt and log hashes, failed snapshots and all
seven candidate attempts are retained locally.

The unchanged serialized profile is 2,048 MiB heap, 1,536 MiB process-tree RSS,
2,048 MiB minimum free memory, one thread, 90 CPU seconds and 180 wall seconds
per module, using only the existing upstream cache. Peak final-check RSS was
1,086,316 KiB; peak source-matched closure RSS was 1,176,760 KiB. No resource
limit was raised. Every owned compiler session was reaped, both locks were
verified free, and the compiler slot was released to the parent.

Compiler repairs supplied explicit tuple arities, opened or qualified existing
helper namespaces, and moved namespace audits into their defining modules.
No frozen mathematical statement, original source, build policy or global
register changed. No full-root rebuild, remote CI or Git action is claimed.

## Remaining source-specific work

This is a generic internal prerequisite toward paper 06 lem:id1. External
identification with the original least-code representative, all-input
calibration of a later exact-one fallback wrapper, and replacement of the
original canonical typed checker remain separate. T-fixed does not mean
canonical for arbitrary leaves. Source-specific representative congruence,
typed invariant propagation, CertifiedApplicationLift and the closed all-term
endpoint remain pending. No numbered source statement is promoted.

## Portable packet and reproduction

Ten InternalBoundedDescentNormalizer Lean files and six concise evidence
files are listed exactly in ACCEPTANCE.json. Raw native receipts, logs,
candidate snapshots and receipt mappings remain local.

    python3 scripts/check.py --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048 --threads 1 --cpu-seconds 90 --timeout 180 LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStatementChecks
