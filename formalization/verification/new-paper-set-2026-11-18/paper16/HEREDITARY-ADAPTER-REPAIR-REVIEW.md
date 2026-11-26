# Adapter proof-only recursion repair review

Read preserved log 1795010359503811677-2 and byte-compared preserved/current adapter: unchanged. Failure is simp maximum recursion depth at the branch using both h and h.symm. The proposed direct `rw [if_pos h, if_pos h.symm]` then explicit attached-mapM `change` and existing attachedMapM theorem avoids reciprocal length rewrite normalization. Negative branch direct if_neg proofs is likewise appropriate. The literal two algorithms and canonicalLower are definitionally aligned after the guards; no semantic target alteration is needed.

Approved this material proof-only tactic replacement before a fresh parent-granted bounded retry, with no recursion/heartbeat/resource cap changes. Preserve original failed edition. This approves design, not applied diff or successful proof. No native execution performed.

Also read HereditaryCoordinateProof.lookupExists: bounded helper scope confirmed. Fits supplies aligned code length; literal schema membership and exact Key equality suffice for actual lookup success. These local premises must later be discharged by real schema/carrier facts; no new final-target assumption is allowed.

Applied delta confirmed: diff against preserved failed edition changes only the approved conditional proof block to direct guard rewrites and explicit attached traversal change. Statement/imports unchanged and all nine frozen hashes verified. Ready for fresh parent-granted bounded retry; no success claim.
