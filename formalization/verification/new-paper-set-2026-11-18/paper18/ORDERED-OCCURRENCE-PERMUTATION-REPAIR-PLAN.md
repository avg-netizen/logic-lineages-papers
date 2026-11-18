# Permutation program proof-only repair after heartbeat stop

Receipt 1795016932613685252-5 was reaped and released. Exact original proof, freeze and receipt/log preserved under ordered-occurrence-failures before editing. No retry has run.

The unchanged slices_primitive body hit 200000 heartbeats at nested list_map composition. Replace the anonymous nested construction with named, fully typed SliceInput/SliceState/SliceStepInput and sliceHead/sliceMap/sliceStep declarations. Separate primitive proofs for head construction, map-element cons, map application, and final cons. The list recursion consumes the named step theorem. This separates elaboration/typeclass workloads without changing insertSlices, rank, children, assemble or actual permutation output.

Ordinary repairs in the same proof file: explicit append definitional calibration; replace nonexistent arithmetic field/power APIs by typed nat_add/nat_mul and square calibration; unfold children before list_casesOn; simplify the empty-list disjunct; import Nlinarith explicitly; use function congruence rather than unavailable List.foldr_congr; destruct the entire assembly input before list cases so the match reduces.

Seven frozen pins remain unchanged. Exact List.permutations order, decreasing two-call rank and internally derived successful assembly still mandatory. Request independent material review before a fresh bounded PermutationPrograms gate. Original memory/RSS/time/heartbeat caps remain unchanged; no computational acceptance yet.
