# Paper 16: exact order inference in the printed Tower Cofinality proof

Source: `16-persistent-marking-termination-ordering/sections/ordinals.tex`,
lines 594–632 (the Veblen-hull critical orbit, the defining clause (P), and
Tower Cofinality). `PrintedTowerCofinalityOrderProof` abstracts the sorts of
indices and values to two linear orders, but retains each mathematical
premise of the proof explicitly. Both suprema are represented by genuine
`IsLUB` of the actual ranges, not invented least-bound assumptions applied
only to the desired conclusion.

* `tower` = a_n, `endpoint` = Λ, `norm` = coefficient norm, `collapse` =
  the particular ψ_B, `critical` = actual N_B-critical orbit membership,
  `floor` = 1, and `limitValue` = sup_n ψ_B(a_n).
* The caller must supply actual strict increase of a_n, its LUB at Λ, the
  actual collapsed sequence LUB, the given coefficient cap and both strict
  lower bounds on collapse values. The control clause at each a_n and the
  exact least-critical predicate at Λ remain hypotheses, as does closure
  of criticals under increasing natural-indexed LUBs. There is **no**
  assumption that ψ_B is universally monotone or that the desired equality
  holds. The source is not based on ordinary critical fixed points.
* The proof derives strict increase of the collapsed tower, takes a genuine
  common natural index via max for the two strict LUB approximations,
  proves the supremum is critical and satisfies (P) at Λ, and obtains each
  inequality by leastness and the actual least upper bound. The endpoint
  is therefore an actual least upper bound of the collapsed sequence.

This discharges only the internal order inference. It does not instantiate
the real Simmons/Veblen-hull objects, prove their calibration, identify the
endpoint with Bachmann–Howard, calculate an original native term rank, or
promote any printed theorem. No native order imports, Ordinal imports, or
change to any blocked gate.
