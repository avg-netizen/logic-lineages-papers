# Internal hereditary-validator termination and saturation

Four more exact contracts are proved in sixteen new Lean modules: complete
actual transition work decrease, singleton/validator identification, internally
proved sufficient-fuel terminality, and two-way fuel saturation. Eight of the
twelve frozen internal recurrence contracts are now checked.

For every raw pending worklist, the proof internally constructs a terminal run
once its payload-only weight is covered. Success is not assumed; either literal
failure or the original empty live state is produced. Both directions of fuel
saturation use this proved endpoint, not an external completed-run premise.
Singleton identification retains the unchanged original payload+1 validator.

All arbitrary binary leaf Programs, malformed raw values and per-frame context
parameters remain in scope. The focused closure has1,183 source-matched modules
and standard-only axioms. Frozen and inherited sources, toolchain and fixed
limits are unchanged. Source-first compact evidence is published; failed attempts
and reconstructible bulk logs remain local. No full-root or remote-CI pass.

Four contracts remain pending: work-append acceptance, exact internal validator
acceptance/output recurrence, and lambda-child closure. Final-source transport,
canonical-body coherence, substitution and paper06 lem:id1 remain pending.
Register:171 checked,2 inherited,16 pending/189. Stop at2026-11-11 17:30UTC
without automatic resumption.
