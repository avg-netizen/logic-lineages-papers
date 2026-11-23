# Indexed abstraction body repair 01

- Failed native gate: LogicLineages.StandardControlCurrent.PolicyIndexedAbstractionBodyStatementChecks
- Failed native log: indexed-abstraction-body; receipt 1795428312397157966-80
- Failed original native log SHA-256: 680bbcbac7a42fba57a484b30cfbc5f062d7c277383df561c7524bfd2bde08df
- Failed proof path: LogicLineages/StandardControlCurrent/PolicyIndexedAbstractionBodyProof.lean
- Reversible failed copy: PolicyIndexedAbstractionBodyProof.lean.failed-source
- Failed leaf SHA-256: 0490df3a62f1c8975ffb189794e52715af6c92fba195d6457645d69545d93d87
- Repaired leaf SHA-256: 22f45d2349eff88163ffee00d4596977594dad4364836c699b4163f9e4e331d0
- Unchanged targets SHA-256: ea50359a5a31e7886465e9830ce9ba7c45799061876bdd249ff0c31b411c8a89
- Unchanged checks SHA-256: d72e5d0a2917933959430c336fb6f9e92da6497d29d54800fbdc9bf60dae05dd

Separate projections/argument pairing from factor, positive request, fallback,
and finishing proof composition using typed named maps and exact pointwise
equations. Split the request cases into independent tests and primitive branch
programs so the checker need not unfold the nested arithmetic/syntax layer.
Existing semantics, exact checks, and native checker settings unchanged.
