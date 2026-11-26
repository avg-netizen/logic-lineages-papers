# Publication recovery, 13 November

The 11:44 local checkpoint waited in local publication-payload assembly for about50 minutes. The expected tree was absent remotely and no create-tree call had been reached. The remote30-minute checkpoint cadence was missed. Read-only reconciliation verified the old head, then the exact checkpoint was published as9ae84054300ab6b9c49f262834b42a653f3b4d51.

The next draft checkpoint's tree was created, but its create-commit call returned an UNKNOWN RemoteProtocolError. No ref update followed. Commit search did not locate a matching commit; an unattached object may exist. That exact operation was not repeated. A distinct newer source checkpoint, including checked Dispatcher and subsequent repairs, was created from the verified parent and published non-force as e60342ff053dd9c840a919cc37a41dacb3b3d68a. Local previous snapshots remain preserved in repository history/reflog and failed source archives. Fetch verified tree equality and the remote ref. No merge or force update occurred.

Payload reads are now bounded sequential batches with persisted offsets, not one long parallel orchestration. Latest source snapshot DRAFT-SNAPSHOT-1245; next maximum checkpoint13:15 UTC. Hard deadlines remain17:40 all-current-work and21:40 stop.
