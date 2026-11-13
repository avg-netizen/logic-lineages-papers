# HistoryRuleSuffix source-scope audit

Status: independent static specification audit complete. Native preflight and candidate proof acceptance are pending coordinator confirmation; no compiler was run by this reviewer.

## Finding

No scope mismatch found in Definitions, Targets, and Preflight relative to the original `GorbowProofChecker.ruleCheck` branches 2 and 3. These are exact native calibration targets plus internal **accepted-branch** suffix laws, not a full proof-checker correctness theorem.

- `NativeMP` compares the explicit five-input program directly to original `ruleCheck h (mpLine n raw r1 r2)`. The original wrapper supplies rule 2 and canonical unused payload fields. The two actual Option-encoded lookups are guarded against zero before predecessor/entry decoding can affect acceptance. Both contexts must equal n; the implication entry must equal `7 :: (antecedent ++ raw)`, exactly original `binary 7`.
- `NativeGeneralize` uses original `generalizeLine`, whose unused fields are canonical. It guards the actual Option lookup and requires premise context n+1 and conclusion `10 :: premise`, exactly original `unary 10`.
- Equality tests both truncated differences. Argument order of `difference` is immaterial to this two-sided equality test. Conjunction and zero/positive selection match Boolean acceptance.
- Internal targets quantify arbitrary source terms and actual registry occurrences of these unchanged programs and append. Their only logical antecedent is old rule acceptance (=1). They do not assume successful lookups, entry reconstruction, well-coded histories, a bound on reference indices, native calibration, or the desired suffix law.
- The accepted `HistoryAppend.InternalPreserveSome` is explicitly conditional on a successful Option lookup. A new internal proof must derive that condition from rule acceptance, rather than silently strengthen the public target. Actual append is h ++ tail, retaining newest-first indices in h, not prepending tail.

## Necessary boundaries

“Preserving missing-reference failure” in a target comment must be read as preserving the checker’s missing-reference **guard**, not as rejection stability under suffix extension. A formerly missing index can become present after append. The formal targets correctly assert acceptance preservation only.

The MP program also uses the same numeric append on encoded `List Nat` formulas. The accepted public `NativeHistoryAppend` statement specializes to `History`; it cannot alone justify that call. Accepted `NativeProof.appendEval`/`resultCons` and generic list codec equations provide the generic list calibration route. This is a proof obligation, not an extra target premise or evidence that calibration has already passed.

No claim here includes `lineCheck` formula validation, arbitrary noncanonical line payloads, proof-run closure, soundness, or internal reflection of native evaluation. Preflight only names the four target propositions and does not prove them.

## Reviewed immutable-source fingerprints

- `LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryRuleSuffix/Definitions.lean`: `4ab64a8316801fa95b5900b279179d854f32ecf42fcb3689d16a93007ceb9f5f`
- `LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryRuleSuffix/Targets.lean`: `35edec2f24c2348e8cf1acd5f9962e50b9c290dfa143f4a4f6532ef7a03b97d4`
- `LogicLineages/ComputabilityKnowledge/CertifiedSourceProvabilityCompletion/SixSol20261113/HistoryRuleSuffix/Preflight.lean`: `226d5d76f654ff10a0be664bc522b8cbda6349ac782406e0f294020063d1d996`
- `LogicLineages/ComputabilityKnowledge/GorbowProofChecker.lean`: `edab7ab6c256d8cb7e7b0f61c5ec55a7cf262b798c52566f4807dcc651071b9e`
