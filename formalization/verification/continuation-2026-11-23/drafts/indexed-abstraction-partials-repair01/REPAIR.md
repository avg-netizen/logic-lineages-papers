# Indexed abstraction partials repair 01

- Failed native gate: LogicLineages.StandardControlCurrent.PolicyIndexedAbstractionPartialsStatementChecks
- Failed native log: indexed-abstraction-partials; receipt 1795428037751840305-33
- Failed original native log SHA-256: 2959f33a853acff30dd33401421523c55bfe0a48395247e2a02f786530c1653c
- Failed proof path: LogicLineages/StandardControlCurrent/PolicyIndexedAbstractionPartialsProof.lean
- Reversible failed copy: PolicyIndexedAbstractionPartialsProof.lean.failed-source
- Failed leaf SHA-256: b9a613080f239e9d16af46c00cb1d2717bfda83ed5e91ca847b555b94696b661
- Repaired leaf SHA-256: dd24804e1250d826dca3e4b5793b571aa63102ee2b1714c6100f6617114d5024
- Unchanged targets SHA-256: f97d161aa3e20e1b457a83ff3bbb3105c148d57af52c6272f7d612df9e593113
- Unchanged checks SHA-256: 7ea1a52cd4bce5f42c3b4c606f057469eb914c5d3b3c4deeb4951a70b46e18c6

Separate the step argument, append, and partial advance from proof of the
bounded recursion. This uses explicitly typed computable functions and shallow
equations instead of elaborating Partrec.map inside Partrec.nat_rec. Checker
settings, semantics, and checked statements unchanged.
