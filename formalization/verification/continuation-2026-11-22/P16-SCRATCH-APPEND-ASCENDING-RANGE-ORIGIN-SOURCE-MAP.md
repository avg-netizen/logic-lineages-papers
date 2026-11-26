# Paper 16: exact physical scratch append and ascending-range origins

Status: source-only candidates; exact native and named axiom checks
pending. Existing forward range, named-leaf, scratch programs and
targets are unchanged.

- `exact_OpenScratchAppendOrigin` is a backward exact rule. Given the
  actual original append output and actual occurrence of one candidate,
  derives an object disjunction that the candidate is in one of the
  exact two source lists. Original object list induction on the left
  list, with right list and candidate fixed, supplies the invariant.
  In the original cons step, recover the actual append tail and exact
  output cons; the real head hit is also a hit on the unshifted source
  head; the right case follows induction on that very append tail.
  There is no independently picked list, numeric reflection, membership
  index, exclusivity, or any priority claim.
- `exact_OpenCoverAscendingRangeOrigin` uses the checked-forward
  component's **unchanged** literal ascending append-right AST and
  input/output graphs. Genuine membership in the reported range implies
  actual object order `i < bound` at that same bound. Proof uses object
  Nat induction, actual recursion at its predecessor report, and the
  premise-free logical consequence of physical append provenance just
  described. The current singleton uses the original standard cons,
  exact head equality and rejecting nil; the earlier component uses
  the genuine predecessor graph and order successor. No assumed range
  calibration, provenance, generic layer transport, or external decoded
  list appears in the exact theorem.
- Named-leaf backward provenance and stage transport are not included.
  A generic backward Cartesian-fold origin statement would need
  explicit same physical block witnesses and does not follow from its
  checked forward member introduction.

| Module | SHA-256 |
| --- | --- |
| `NumberedWindowInternalScratchAppendOriginChecks` | `1d3a67597c1a2cedcfa79610c806ae679b9572d35b14c736a136cb19b2306649` |
| `NumberedWindowInternalScratchAppendOriginSyntaxProof` | `281ea805df0d8220f6ebbaed5c7b47156f91b8b10ebdcb324a99be71930eadcb` |
| `NumberedWindowInternalScratchAppendOriginTargets` | `eee23d598709e2d218713bc25d387276d5ca571ee57c142980ee541ecc6a5957` |
| `NumberedWindowInternalCoverAscendingRangeOriginChecks` | `192353dca35c40c4d64c81f03cb7cfd39bf3352e7c16457e8ae3a9914fba54a0` |
| `NumberedWindowInternalCoverAscendingRangeOriginDataProof` | `62bcec7915057c09f339d263ce2f63cff854556ad8fb3c4e17e9ec0ddfb15884` |
| `NumberedWindowInternalCoverAscendingRangeOriginSyntaxProof` | `555b3aba5607f5c1e38f658cfa95eefc7d1ac9f3ffd931a1d4b2431713296442` |
| `NumberedWindowInternalCoverAscendingRangeOriginTargets` | `0c0d5cffcb9070e4fe532cdb11eab1c64df4dedc64b7d6ce5949607a1ab7a86b` |
