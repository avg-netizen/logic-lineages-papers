# Original path-certificate coding and structural application lift

Date: 7 November 2026.

The nine frozen targets use `NumberedQuotientPathCertificates` and
`ID1Completion.ApplicationCertificateLiftPath` exactly as defined by the
existing source modules. A path is the original natural-list encoding of the
pair codes of its edge entries. Decoding is the original natural-list parser
followed by `Nat.unpair`. No new codec, validity predicate, or transformed
certificate representation is introduced.

The first five targets prove total unique decoding, both inverse equations,
encoder bijectivity, the exact decoder/encoder equivalence, and literal nil/cons
decoder equations for arbitrary natural tail codes. The accepted
`NumberedMultisetNumericTotalityProof` supplies totality of the unchanged
natural-list parser; the existing path round-trip theorem supplies the forward
inverse.

The remaining four targets concern the existing `liftPath`: it commutes with
decoding, preserves decoded length, preserves and reflects the empty path and
zero code, and satisfies exact nil/cons equations on all input codes. The
constructor equation retains the original `vertex` and `liftEdge` functions,
including their existing behavior on malformed typed inputs. These are coding
and structural laws, not acceptance of an invalid edge or path.

The length and emptiness laws quantify `liftPath` at an explicit ambient
`Gamma`. They do not assert those laws for the outer `pathValue` wrapper on a
malformed argument-object code: that wrapper still has its original zero
fallback when the argument object fails to decode.

This is a supporting consumer for paper06 `lem:id1`. It does not construct an
internal certificate-lifting derivation, prove source-specific computability
closure, or promote a numbered statement. The numbered register is unchanged.

The target bytes and original source dependencies were recorded in
`FROZEN-TARGETS.json` before proof authorship and remain unchanged.

## Focused acceptance

The serialized `NumberedQuotientPathNumericTotalityStatementChecks` gate passed
with nine exact aliases, each using only `propext`, `Classical.choice`, and
`Quot.sound`. The three new modules passed on their first Lean run. The focused
run compiled 37 modules with peak observed process-tree RSS of 1,207,760 KiB,
under the unchanged 1,536 MiB cap. Heap, CPU, wall, thread, and free-memory
limits were unchanged; no upstream dependency was rebuilt.

The command was:

```text
python3 scripts/check.py --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048 LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathNumericTotalityStatementChecks
```

The exact final alias audit is preserved in `path-numeric-totality.log`.
The local receipt is `build-reports/1794091287229002506-2.json`. This focused
acceptance is not a full-root or remote-CI build.
