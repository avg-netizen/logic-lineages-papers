# Thin native attempt: resource blocker remains

Receipt `build-reports/1794978270737441690-2.json` (copied as THIN-NATIVE-RESOURCE-STOP.json). Unchanged original caps and pinned toolchain. New polynomial definitions passed at1,286,136KiB RSS; new rational definitions passed at1,549,804KiB. ThinTargets stopped at1,574,880KiB, exit77, before any new proof module. Queue released and process reaped. No same-input retry, cap increase, source edit or supporting acceptance follows.

The isolated graph removed series but essential Perfect plus RatFunc.AsPolynomial already consumes almost the whole ceiling. Splitting targets might move the failure slightly, but cannot be presented as a reliable remedy for later Degree/tactic imports. The proof candidate remains untested.

A more substantial source-exact alternative would avoid AsPolynomial and Degree entirely: use RatFunc.Basic, define the indeterminate as algebraMap Polynomial->RatFunc of Polynomial.X and constants through the actual coefficient embedding, and prove rational square-decomposition uniqueness by clearing denominators and comparing polynomial degree parity. This would require a superseding reviewed target freeze, literal actual field embeddings and new proofs; it cannot reuse the intDegree proof. It is only a possible future plan, not performed here. No surrogate abstract field/state is proposed.
