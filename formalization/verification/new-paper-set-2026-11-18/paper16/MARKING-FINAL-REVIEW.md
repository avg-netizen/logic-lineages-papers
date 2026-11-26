# Independent final marking review

Approved as two supporting bundles, not numbered-paper completion. Re-ran the
read-only evidence reconciliation:8 local modules,9 exact aliases, zero errors.
Inspected current typed proof and aliases; both original freeze manifests still
match. The binder-case repair changes proof only. Exact compiler/input/output/
source/cache profile and logs reconcile under the unchanged core-only profile
(heap1536MiB, RSS512MiB, CPU90s, wall180s, one thread). Actual alias axiom logs
contain only propext and Quot.sound. No sorry/native_decide/extra axiom.

Scope caveats in both pre-scope reviews remain: raw laws are annotation laws;
typed companion preserves the declared named auxiliary typing, not alpha
quotient/signature correspondence or full comparison. No aggregate/full-root/CI
claim. No new compiler run was performed by this reviewer.
