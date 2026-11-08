# Parameterized original path checker

This component supplies the runtime-parameter version of the existing concrete numeric path checker needed by the uniform application-certificate argument for paper06 `lem:id1`. It does not claim the path lift, the unqualified `CertifiedApplicationLift`, or any remaining multiset, constructor, lambda, substitution or all-term theorem.

The edge program reads `[source,target,certificate,parameter]`. The path checker reads `[source,target,rawPathCode,parameter]`. Its summary uses the existing `InternalRawListRecursion.listRec` at `k=2`, with `[target,parameter]` as the unchanged parameter tuple. A nonempty summary retains the original paired first entry and suffix acceptance in one original cons cell. The source path, vertices and edge certificates are not re-encoded to contain the parameter.

The exact frozen targets are two external calibrations and four internal graph equations. External calibration is to the unchanged `NumberedQuotientPathCertificates.pathTest` and `positivePathTest` on every raw natural code, under the exact original edge-test calibration at the displayed parameter slice. Decoder success is not an additional premise. The internal targets quantify arbitrary arithmetic terms for the parameter and require no external calibration: ordinary nil accepts exactly equal endpoints; positive nil rejects; either cons checker accepts exactly when its first edge and reflexive suffix accept at the identical parameter.

Proof suppliers are the existing arbitrary-parameter raw-list recursion nil/cons graph laws and all-input evaluation, original list-code and pairing graph laws, exact-one conjunction/branch laws, total path decoding, and Program totality/functionality. The previous fixed-arity checker modules provide the proof structure; their frozen sources remain unchanged.

The subsequent application-path lift will reuse `InternalApplicationPathMap.pathMap` verbatim, with its old context slot carrying the parameter: vertex inputs `[parameter,domain,codomain,RAWargument,value]` and map inputs `[code,parameter,domain,codomain,RAWargument]`. The original `edgeLift` is unchanged. That two-target list-induction consumer requires a separate specification and proof; no whole-path compatibility premise is introduced here.

The two specification files and named suppliers are pinned in `FROZEN-TARGETS.json` before proof construction, against base `fd5936d8396b90e17767bc59c82a061178fe4378`.
