# Internal recurrence: first supporting checkpoint

Three of twelve frozen internal contracts are proved in thirteen new Lean
modules: bounded-validator acceptance implies actual node factors; payload-only
work-fuel zero/cons equations; and zero weight iff empty work. The acceptance
proof uses the original payload+1 fuel, first-step rejection and independently
proved failure absorption, without assuming a successful node or residual run.
All witnesses and graph implications are internal arithmetic derivations.

The explicit proof-support weight counts only raw payload+1 per frame. It does
not replace or occur in the original validator and does not count Gamma/type
codes. No native calibration/reflection, successful-run, child-validity or
termination premise is supplied. The focused closure has 1,141 source-matched
native modules and standard axioms only. Fixed limits and prior accepted
sources remain unchanged. One preflight-only missing namespace binding was
archived and repaired before proofs; its statement meanings were unchanged.

Nine contracts remain pending: weight append, transition decrease, sufficient
fuel, saturation, work-append acceptance, singleton identification, full internal
acceptance/output recurrence and lambda-child closure. Pending candidates are
not accepted by this checkpoint. Final-source reconstruction, canonical body,
substitution and paper06 lem:id1 remain pending; register171 checked,2 inherited,
16 pending/189. No full-root/remote-CI pass claimed. Source-first, compact evidence;
bulk attempts remain local. Stop at2026-11-11 17:30UTC without automatic resumption.
