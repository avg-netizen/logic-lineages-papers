# Paper 16: order facts around the tower endpoint (conditional, over #1463's abstract data)

Frozen `LogicLineages/PersistentMarking/ConditionalTowerEndpointTargets.lean`
(sha256 `232983db9ae9b0a41fd6e59f15552dfef140f8c8537bd58e0516c75e109c624d`), all under `TowerHypotheses D`:
- `TowerEndpointIsSupremum` — the endpoint is the least upper bound of the tower arguments
  (the paper's Λ = sup a_n), from "below" and "cofinal" alone.
- `TowerValuesBelowEndpoint` — every collapse value along the tower is strictly below the collapse at the
  endpoint (the "conversely" half of the printed proof of `lem:tower-cofinality`, as its own statement).
- `TowerSupremumNotAttained` — no tower value equals the supremum of the tower values (the tower-level
  content of the remark after `thm:height`, "No individual term has been assigned rank BH").
Proofs are a few lines of order reasoning on top of #1463. Receipt `1795405097075538833-3293135`.
Supporting only; the hypotheses are uninstantiated.
