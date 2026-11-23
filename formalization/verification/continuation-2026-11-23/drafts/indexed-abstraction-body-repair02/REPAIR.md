# Indexed abstraction body repair 02

- Failed native gate: LogicLineages.StandardControlCurrent.PolicyIndexedAbstractionBodyStatementChecks
- Failed native log: indexed-abstraction-body-repair01; receipt 1795428836536478214-39
- Failed original native log SHA-256: d3160809633eefd0c69bd91bb23116823da1a7cecc4698a161978a40e51a5c1a
- Failed proof path: LogicLineages/StandardControlCurrent/PolicyIndexedAbstractionBodyProof.lean
- Reversible failed copy: PolicyIndexedAbstractionBodyProof.lean.failed-source
- Failed leaf SHA-256: 22f45d2349eff88163ffee00d4596977594dad4364836c699b4163f9e4e331d0
- Repaired leaf SHA-256: de3ced5149d2614ff619c2dba270b704289b6dd0d61e18b9d4eec0be12bbef4e
- Unchanged targets SHA-256: ea50359a5a31e7886465e9830ce9ba7c45799061876bdd249ff0c31b411c8a89
- Unchanged checks SHA-256: d72e5d0a2917933959430c336fb6f9e92da6497d29d54800fbdc9bf60dae05dd

The remaining error was at the composition that projected the level out of
the multi-field factorArgs tuple. Replace it with a direct primitive projection
proof and separate level+2 proof. Existing semantics, exact checks, and native
checker settings unchanged.
