# Checked: parameterized canonical result fold

Four exact internal targets passed for the unchanged original result-stack programs, one shared four-binary-leaf `Data`, arbitrary contexts and a symbolic runtime parameter. `InternalParameterizedCanonicalResultFoldProof.internalLaws` assembles the four laws for that same data tuple.

The checked targets prove:

- Actual input source validity and its original type field, together with an actual raw fold output, imply successful execution, output source validity, preservation of that original type field, and fixedness under the same descent transition.
- Input source validity and type alone produce an internally quantified output carrying both actual fold/success graphs and the full invariant.
- An actual requested-type membership graph additionally gives acceptance by the existing ternary canonical typed checker.
- The original raw application and actual application program transport a function's fold output to the parent's certified output, retaining the necessary actual codomain-membership premise. Parent validity is derived.

## Proof route

The opening proof recovers the original children, codomain and strict child-payload bounds. Full internal strong induction quantifies input, requested type and parameter inside its payload predicate. Rejected openings use the actual fallback descent. Accepted openings obtain both child outputs internally, prove source validity of their original raw application using both validator branches, and apply the unchanged certified stack closure and descent invariant. Program functionality identifies the internally produced output with an independently supplied actual fold graph.

Representative application transport queries both original child payloads and the argument's actual fold output internally. Its concrete application program normalizes only the raw argument before the same combine; no fold-idempotence or fixed-argument premise is introduced.

## Acceptance

The final native gate is `InternalParameterizedCanonicalResultFoldStatementChecks`, receipt `build-reports/1794171843877217849-5.json`. All four exact aliases and `internalLaws` depend only on `propext`, `Classical.choice` and `Quot.sound`. The serialized 2048 MiB heap / 1536 MiB observed RSS / 2048 MiB minimum-free profile remained unchanged.

Both frozen specification files retain their original hashes. Compiler repairs were confined to two namespace opens and spacing between adjacent closing brackets in a nested proof-local vector. Successful current-source rows from the earlier focused runs remain available in receipts `1794171582059839622-5.json`, `1794171638894086795-5.json` and `1794171815461548167-5.json`; the shared acceptance collector stages those rows and source pins.

This component proves internal laws without semantic calibration premises. The all-input original representative calibration and uniform external selection are a separate component. The unrestricted original certificate lift, multiset/constructor/lambda/substitution arguments and closed all-term endpoint remain separate source obligations. No numbered statement or global register status is promoted here.
