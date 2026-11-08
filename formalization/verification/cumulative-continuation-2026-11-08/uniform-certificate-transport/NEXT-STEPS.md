# Next formalization step

The 21 targets in this checkpoint are accepted. Continue from the actual selected programs; the completed arithmetic, canonical fold, context-only membership, generic step equations and generic path induction do not need to be reopened.

## Programs and parameter order

| Program | Original input order |
|---|---|
| Binary validity, target validity, member, representative and result fold | `[value,parameter]` (member uses the type as its first coordinate) |
| Selected typed checker | `[value,type,parameter]` |
| Actual canonical application `actualJ` | `[domain,codomain,canonicalFunction,RAWargument,parameter]` |
| Selected structural endpoint | `[domain,codomain,source,target,argument,parameter]` |
| Selected step checker and future quotient-edge checker | `[source,target,certificate,parameter]` |
| Parameterized path checker | `[source,target,rawPathCode,parameter]` |
| Existing application-map vertex | `[parameter,domain,codomain,RAWargument,value]` |
| Existing application path map | `[code,parameter,domain,codomain,RAWargument]` |

The parameter is the original `pair(contextCode,encode Gamma)`. Internally its Gamma coordinate remains symbolic. The mapper and original `edgeLift` are reused literally; the parameter must not be inserted into the source certificate encoding.

## Concrete quotient edge and application vertex

`InternalOriginalUniformApplicationStepSelectionProof.actualOriginalUniformApplicationStepSelection` chooses one oldStep Program4 for each globally calibrated Data tuple, before every source window and Gamma. It supplies the concrete selected step core, all-input original step calibration and the internal full-output application-step law. The endpoint program is exactly `InternalParameterizedStructuralEndpointGuard.selectedEndpoint data`.

Parameterize the original outer source/target/same-type guard and quotient-edge representative comparisons using that step core and the same normalized Data. Preserve the original source-universe filter and packed-target semantics: source representative selection is guarded by source validity; target representative selection must not gain a source-universe restriction. Recover and rebuild the literal original certificate selectors internally.

The canonical application-typing theorem now gives the actual result type at symbolic p. Endpoint factorization gives the function/argument tags and raw validity premises. Existing parameterized canonical representative transport supplies the relationship between canonical source application and the original lifted raw endpoint. Combine these with the selected step law to derive the concrete local edge invariant and vertex compatibility, without assuming those source-specific rules.

Instantiate `InternalParameterizedApplicationPathLiftProof` with those actual local rules. Its reflexive and positive theorems retain the original map, supplied output vertices, edge certificates and exact mapped output. The generic theorems already prove whole-path transport from the local rules; they do not by themselves prove the concrete quotient-edge rules.

## Original outer object/context wrappers

Use the existing original same-Gamma guards and left/right selector graphs to obtain one shared runtime Gamma code for the function, target and argument. Construct the symbolic parameter `pair(context,gammaCode)` internally. The concrete member slice and uniform application typing already handle this parameter without a preselected Gamma.

Rebuild every original output/certificate acceptance factor, including same-Gamma, target typedness, common raw type, window checks and the original positive path checker. Discharge the unchanged original `CertifiedApplicationLift` antecedent. The old fiber-qualified theorem remains a useful supplier/template, but its extra fixed-fiber graph is not a consequence of that antecedent.

Then apply the existing full-type downward-closure consumer. The separate source multiset, constructor, lambda, computable-substitution and closed all-term ID1 accessibility derivations remain necessary for numbered completion.
