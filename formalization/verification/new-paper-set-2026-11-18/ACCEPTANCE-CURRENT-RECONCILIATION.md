# Current acceptance integrity reconciliation

The read-only `reconcile_current_acceptance.py` audit reconciles the
current accepted directory. The JSON report records its packet/module/path counts.
The JSON report timestamps this check. No recorded source/output/evidence drift
was found. It checks every accepted evidence-file hash, module source and listed
output hash, plus receipt/log hashes where those hashes are recorded.

Core-only paper16 evidence uses embedded native rows without separate receipt/log
hashes. This audit does not independently rehash every underlying core receipt or
log. It does not replace the original recursive packet verifiers, independent
source-scope reviews, the migration/register bijection check or compiler runs.
No full-root build or CI result is asserted. Later work can make this snapshot
stale; rerun the read-only script to reconcile the current acceptance directory.
