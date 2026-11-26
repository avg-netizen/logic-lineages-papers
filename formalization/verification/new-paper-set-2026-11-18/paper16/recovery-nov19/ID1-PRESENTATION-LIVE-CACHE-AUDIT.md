# Paper 16 arithmetic presentation and live cache

Read-only replay on November 19, 2026, Chicago time, at the original formalization path. The current checker recomputed the recursive source, direct external object, dependency bundle, compiler, toolchain, and search-path input keys. Its ordinary cache validator matched the original outcome, output bundles, logs, and receipts at a 2048 MiB Lean heap cap, 1536 MiB process RSS cap, 90 CPU seconds, 180 wall seconds, and a single thread. [Checker](../../../../scripts/check.py) · [Run policy](../../../../.local-run-policy.json)

| Existing root | Current live cache hits | Original root wall / CPU | Original root peak RSS |
| --- | ---: | ---: | ---: |
| `OrdinaryArithmeticProgramProof` | 15 / 15 | 1.379 / 1.27 s | 879,292 KiB |
| `ID1Completion.InternalCalculusDefinitions` | 699 / 699 | 2.346 / 2.24 s | 1,012,612 KiB |
| `ID1Completion.SourcePresentationSupportProof` | 706 / 706 | 1.531 / 1.47 s | 987,868 KiB |
| `ID1Completion.SourcePresentationStatementChecks` | 706 / 709 | Three current wrapper cache misses | — |

The first three row metrics come from `build-reports/1794271668294249378-2994094.json`. The numbers include the calculator dependency resolved by the original checker. Only three matching old source and object pairs were present in the separate isolated Mathlib stage. A narrow new modern leaf can reuse the original live cache under the same safeguards and the serialized queue. Its own peak RSS remains to be measured.

## Prospective formula adapter

The exact new program interface accepts one numeral for either domain and `(source, witness, destination)` for the certificates. The retained source presentation expects two-argument domain programs with order `(context, address)` and four-argument certificate programs with order `(context, source, destination, witness)`. Fix the actual signature and window first. Compose each domain program with projection 1 and each certificate program with projections 1, 3, 2, using zero-based slots. The new addresses already carry their lexical contexts and result types. Close the unused numeric context slot at the literal numeral zero. [Current program interface](../../../../LogicLineages/PersistentMarking/NumberedWindowAddressCheckersProgramTargets.lean) · [Retained presentation](../../../../LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourcePresentationDefinitions.lean) · [Certificate graph](../../../../LogicLineages/OrdinalComparison/TerminationOrdering/OrdinaryArithmeticQuotientDefinitions.lean)

The bounded target would prove the literal semantical equations for both tagged branches of `sourceBody` and for `allTermsFormula`. For every predicate `P`, the even and odd clauses use their respective unary program returning 1 and require `P` at each same-tag successor for which the actual ternary program returns 1 on some supplied certificate. The all-terms formula says that every scalar program input returning 1 belongs to the even slice of `P`. The existing graph realization, tag isolation, and substitution lemmas provide the immediate proof ingredients. The comparison with Paper 16's all-input source checks and the object-theory derivation require separate checked endpoints. [Graph truth](../../../../LogicLineages/OrdinalComparison/TerminationOrdering/OrdinaryArithmeticProgramProof.lean) · [Certificate truth](../../../../LogicLineages/OrdinalComparison/TerminationOrdering/OrdinaryArithmeticQuotientProof.lean) · [Tag isolation](../../../../LogicLineages/OrdinalComparison/TerminationOrdering/TaggedArithmeticOperatorsProof.lean) · [Presentation support](../../../../LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourcePresentationSupportProof.lean) · [Original external operators](../../../../LogicLineages/PersistentMarking/NumberedWindowExternalIDOperators.lean)

## Source pins

```text
fefa8d645edc1c7bd1e4abc750cfaa6556adfc6cc80d6aecaff952192322a144  scripts/check.py
f6c0cb589e515b5a3316a342db0485542b6cd865e5d51f9fbb6a53b02069416f  .local-run-policy.json
557cb2999f699e7959a91fd9f52b3207ebaa5ee3e2b51dd103b64013af71d85d  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/InternalCalculusDefinitions.lean
ecfdbfa32e9c4b988e53236cf284f025d30aded970487fc8da6c1a99f7a61ec7  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourcePresentationDefinitions.lean
341522f3449a87739e52e6f84e1052021a3a39bf11c832e08f63aa21e6dea09b  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourcePresentationSupportProof.lean
4555475b5a8a19ddd29162ca1ed87200537a747e40096cf7ae0b94fe9b339697  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourcePresentationTargets.lean
b787f83e8452a3b0ed2f0f93d52b4afb38186720f2b47bb1c5ad0baedf83bfab  LogicLineages/OrdinalComparison/TerminationOrdering/OrdinaryArithmeticProgramProof.lean
ecc89e1372874af8557d7dacd608b478ae687cb34b85b35e9d877de674adb22c  LogicLineages/OrdinalComparison/TerminationOrdering/OrdinaryArithmeticQuotientDefinitions.lean
757bc713c445759b410ddac16c2481ec8b37de83f536d45781da3cff868d7bf2  LogicLineages/OrdinalComparison/TerminationOrdering/OrdinaryArithmeticQuotientProof.lean
f76724ea239f3e42c8addcb79f3da470d0aa5716b388d45fbc80fd6bc3af0dcd  LogicLineages/OrdinalComparison/TerminationOrdering/TaggedArithmeticOperatorsProof.lean
29ac0460ac6b984a671727f62fd33e4328516319991b8b41fbecf02ad9b03791  LogicLineages/PersistentMarking/NumberedWindowAddressCheckersProgramTargets.lean
aa714c56768639b0267a9c4b19a16448c9044756c379cf1a829bd440fe036773  LogicLineages/PersistentMarking/NumberedWindowExternalIDOperators.lean
```
