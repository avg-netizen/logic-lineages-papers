# Actual family vector coding and equation (C): next staged plan

Source reread: decision.tex lines81–97 and176–201. This packet constructs the constructor-family carrier, not the structural interpretation/operator or adequacy. Prior parameter enumeration retains literal source head, output type, port context, all original positional bases and canonical extra downsets. Source coverage derives declared types from actual ordinary input inventory. The current family-parameter supporting final is pending.

## First coding stage

Use exactly the distinct `MarkedFamilyParameters.schema E heads`, with bounds equal to actual output carrier cardinalities. Enumerate literal Nat vectors with `vectors (schema.map Prod.snd)`. Lookup traverses the actual parameter keys and vector together, comparing via the proved five-field parameterEq. Its result is Option Nat; output binds that result to the actual D_tau(Gamma) carrier's optional index lookup. Neither absent key nor out-of-bounds index is silently successful. Supporting endpoints: raw vector membership iff Fits; unique coordinate with exact output bound; every valid parameter has successful output in its actual carrier for a fitting vector; exact code reconstruction from all valid coordinate outputs. The coordinate length and actual index inverse proofs are derived, not caller-provided.

An uncoded family is `Parameter → Code`. Validity requires output membership on the exact valid parameters. Equality only quantifies over valid parameters. Encoding traverses the canonical schema and searches the actual output carrier; use an Option Code encoding that fails on missing membership, avoiding a default masquerading as success. Decoding may use [] off valid coordinates only, with valid-coordinate successful lookup established first. Prove both semantic and code roundtrips, actual encoding success from valid output membership, and no dependence on function values outside the literal parameter domain. No parent-relative carrier or across-context equality of indices.

## Coherence stage

Define input order only for identical head/output/context: actual positional `tupleLe` at f.arguments plus literal inclusion of canonical extras. Require output order in the actual global output descriptor. Monotonicity Boolean test enumerates every valid parameter pair, including equal/empty tuples and empty extras; ignore nonmatching head/output/context rather than coercing them.

For every valid p=(f,tau,Gamma,bs,es) and every well-formed Delta extending Gamma, form exactly
`p'=(f,tau,Delta,restrictTuple E Gamma Delta f.arguments bs,MarkedExtras.weaken E Gamma Delta es)`.
Prove p' valid internally using actual tuple and extra restriction results. The executable test requires BOTH actual output lookups successful and literal code equality
`(descriptor E tau).restrict Gamma Delta (output p) = output p'`.
This is equation(C), not integer index preservation; no inverse lifting of downsets or tuples. Define retained codes by fitting vectors filtered by the two tests and prove iff full uncoded monotone coherent validity under decode, plus encoding completeness for every valid family. All failed lookups rejected; impossible valid cases paid by coordinate membership. Source-head/declared-base coverage stays in the source instantiation bridge, not an added restriction on arbitrary finite table builder heads.

## Full family lattice stage

Actual pointwise order, joins and meets are computed using global output descriptor operations at every literal parameter. Encode these pointwise outputs only after actual carrier membership is proved. Retention follows from output membership, actual carrier order universal properties (monotonicity in base/extra arguments) and actual restriction preservation of joins/meets (C). Empty input families are explicit: coordinatewise join[] and meet[], not an arbitrary default. Derive finite carrier enumeration, partial order, all finite join/meet universal properties, nonempty carrier, and mathematical completeness by finite filtering. These are fresh full source-family gates, not inferred from vector finiteness alone. No same-type recursive law or generic lattice oracle is needed: the already accepted concrete hereditary output operations supply every law.

Future interpretation tests, downclosure losslessness, operator endomorphism/monotonicity, effective stabilization, and judgment adequacy remain separate. No ordinary source size cutoff or staged application equation enters this representation.

Request independent conceptual review before new definitions or exact freezes. Each coding/coherence/lattice exact scope will then be frozen and independently reviewed before proof/native.
