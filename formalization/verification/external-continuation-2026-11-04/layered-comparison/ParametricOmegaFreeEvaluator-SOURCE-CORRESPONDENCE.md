# Computable omega-free ordinal syntax evaluation

Target-only proposal toward paper09 hardness.tex lines316–319; this is an ordinal-expression evaluator, not the whole source evaluator.

The raw leaf returns1 only for exact code1, looks up env[n/8] with default0 for variable tag3, and returns0 otherwise. In particular omega code2 and malformed atomic payloads are explicitly totalized to0. Branches4/5/6 use natural addition, 2^a*b, and the calibrated actual finite-pair collapse; other branch tags return0. The existing raw fold is unchanged.

UniformComputable assumes a first-order Computable H : Nat×Nat→Nat and is joint in control index, finite environment and arbitrary raw code. Semantic calibration is separate and requires actual OmegaFree encoded syntax plus the explicit environment lookup equations. The generic statement uses an arbitrary variable index map; the typed specialization uses the exact existing componentCode with both de Bruijn variable position and ordinal coordinate intact.

No semantic validity is inferred for malformed or omega-containing inputs. No finite environment construction, source assignment composition, positive output, whole source evaluator, PR value/runtime, source upper bound/completeness or publication is claimed. Generic semantic calibration itself needs no computability or growth assumption on H.
