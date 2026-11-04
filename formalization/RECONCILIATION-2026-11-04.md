# Recovery of the unpublished AG468 checkpoint

The uploaded `logic-papers-unpublished-reconciliation-20261104.zip` has been
reconciled locally on `formalization/reconcile-unpublished-2026-11-04`.
The branch starts from fetched GitHub main
`43a6dceb5804318d72baad25b64212c21db87c32` (merged PR7), which contains the
archive's exact AF101 base, `f1fb833597e3706024fc60c021bc72a4bfed953f`.
GitHub's external branch still pointed to that AF101 commit at fetch time;
none of the archive's paths appeared in either fetched tree. The final AG
publication attempts described in the handoff had therefore not reached
either fetched branch. The source recovery is local and has not been pushed.

| Material | Already published AF101 | Recovered addition | Combined checkpoint |
|---|---:|---:|---:|
| Components with external independent acceptance records | 32 | 139 | 171 |
| Exact statement aliases | 101 | 367 | 468 |

Commit `d91271ece194d9a29199dbe7124cff8e1430e6fe` restores the 781 additive
files of the accepted checkpoint. Its focused module is
`LogicLineages.ExternalCheckpoint20261104AG`. The reported external compiler
and allowed-axiom results are preserved in
[the AG validation record](verification/external-continuation-2026-11-04/CHECKPOINT-AG-VALIDATION.json).
Those compiler results have not been independently replayed locally.

Commit `ba3fb2938dbb817fd0532a052fa90a4a9c605841` separately preserves the
11 source/dependency files for **GroundLambdaTower1** and
**ZeroPatternSubstitution3**. They retain their external individual
compilation-passed status and **pending independent review** status. Neither
is imported by the accepted AG aggregate or the repository root.
PolynomialFamilyLift2 is present in the accepted checkpoint.

Local source checks passed:

- ZIP CRC, archive membership and all 793 manifest file hashes match the
  extracted bytes; all 794 ZIP entries are preserved. Archive SHA-256:
  `07e9349cc4b20d31d79f2290fe249084c784f8d9deb7537d4901c7c9423db208`.
- All 811 source hashes in the external AG validation record match.
- The aggregate contains 468 distinct, consecutively numbered aliases with
  exactly the manifest's declared target names and suppliers.
- The import graph is acyclic, contains the reported 1,953 local modules and
  76 upstream imports, and has no missing local imports. The available upstream
  cache covers the checked non-core upstream imports. Both draft import graphs
  are present. The project's placeholder/added-axiom source scan passes.
- Every file inherited from fetched main is unchanged. The root does not
  import AG, and the numbered source register is unchanged.

See [the local integrity report](verification/local-reconciliation-2026-11-04/STATIC-VALIDATION.json)
and the original [archive handoff](../RECONCILIATION-README.md) and
[SHA-256 manifest](../RECONCILIATION-MANIFEST.json). The local source-graph
fingerprint uses a stated serialization; the external closure fingerprint's
serialization was not supplied and its hash was not independently recomputed.

Keep the qualifications in
[CHECKPOINT-AG-STATUS.md](verification/external-continuation-2026-11-04/CHECKPOINT-AG-STATUS.md)
and the component correspondence documents. In particular, the fixed-b coded
restricted-language classifications do not establish unrestricted paper-language
identity; primitive recursion retains its fixed-b and input-dependent iteration
scope; logarithmic size measures pre-aggregation nodes; termination results
retain their explicit context, calibration, confinement and image-computability
premises. No new whole-source promotion follows from recovery.

Local research and compiler guards remain paused. This reconciliation performed
no local Lean replay, full-root build, CI run, dependency download or publication.
Independent review of the two drafts and a bounded compiler replay are separate
remaining validation work, rather than completed results of this source recovery.
