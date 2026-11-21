# Second November 21 workspace recovery

The executor again went offline after the published Paper 16 raw-minimum
occurrence acceptance. The ref was independently read at
`651eb71f2c7f1ad80ea8cd9dbeb14f7d7f913984`, tree
`af011c036dd2711d7d9d7e093ef72c14031f4c4b`. That immutable checkpoint has
fresh supporting evidence through 733, including the full 1140-module
raw-minimum parser occurrence closure. No lost subsequent local check,
receipt, or idle queue is treated as a successful result. All the separately
source-reviewed proof candidates were already public at that checkpoint.

After workspace-write returned, the current branch was fetched into a new
isolated clone and the same official Lean release restored. Release SHA-256
`ce6e79dd19ea03c0bc17f9d565c3bac20cd2884561e3b431e5b293c1fbb2b5b3`;
Lean reports upstream compiler commit
`b4812ae53eea93439ad5dce5a5c26591c31cb697`, binary SHA-256
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
All nine git packages were checked out at their recorded revisions, and
official same-pinned caches restored for the 70 direct Mathlib roots in the
scheduled recursive closures. No checker, lock, limit, compiler pin, Mathlib
pin, manuscript, or CI changes were needed. Earlier exact failure archives
and independently reviewed proof-only repair02 remain unchanged.

The fixed serialized queue restarts with collector repair02, directed seen
numeric, concrete count pair, directed seen open, and prepared-strip semantics.
Prepared-strip CodeExact follows only if the exact repinned collector
EffectiveProof compiles. The filter and count-congruence target-only gates
follow. Every proof claimed later must have new actual gate and independent
source/object evidence. The owner-numbered inventory remains 156 checked
and 11 pending; supporting credit is separate. The absolute stop is still
2026-11-21 23:00 UTC. No merge or force publication.
