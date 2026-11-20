# Actual new endpoint-guarded address report

Target freeze only. Paper 16 `ordinals.tex` 65–96 uses actual arithmetic
certificates for the positive class path with typed carrier checks. This
supporting characterization opens the exact wrapper, not the still missing
arbitrary-open semantics of the selected raw/least programs.

Fix actual `old = addressPositive cv tv raw least` and
`r = withEndpointCarriers i old`. The original open #674
`someAddressPositive` is the same four-slot block: common packed context
and requested type, both visible raw least fields, both real endpoint
tag/arity reports, the actual context/type validation graphs, and the
selected positive fold on the same supplied witness. The only added
conjuncts are the **actual program graphs at one** of the same (i)
at the original left and right terms. Neither follows from merely
parsing or asserting the old report.

`ExactOpenEndpointRefinedReport` requires an object derivation of
((mathrm{accepts}	omathrm{guardedReport})land
(mathrm{guardedReport}	omathrm{accepts})) under arbitrary fixed
(B,Gamma) and open left/witness/right. Forward: assume the actual
refined acceptance, use #693's actual wrapper elimination, then #674
`forward` at that same body/hypotheses to open the old acceptance.
Retain both actual (i)-graphs. Backward: assume the entire guarded report,
apply #674 `backward` directly at the same body/hypotheses to its original
report conjunct, preserve both actual (i)-graphs, and apply the same
literal conjunction/slot-0/slot-2 reconstruction as #694. Discharge
each actual hypothesis using original implication introduction, and
give actual conjunction introduction. The witness is unchanged in both
directions, no logical truth of an unexecuted program is reflected.

`ExactInstalledEndpointRefinedReport` uses that same arbitrary-body
derivation instantiated at `sourceBody (data i j r d) c` for every
outer (c) with empty hypotheses. This produces precisely the new
guarded report that #696 does not transport from #676's older body.
Keep both existing accepted body/report theorems unmodified. No relabel
between different bodies, no new selected tuple, full matching, raw/least
semantics, neutral computability, or accessibility claim. Original
serialized Mathlib 2048 heap/1536 RSS/2048 min-free/90 CPU/180 wall/thread1.
