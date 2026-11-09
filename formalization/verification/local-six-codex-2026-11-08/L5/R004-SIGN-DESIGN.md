# Actual terminal sign argument (candidate design, not accepted)

The runtime partitions literal current leaders and takes the greatest nonempty
label class. Every label vector is enumerated syntactically; count-below
labels witness coverage only in the proof. No guard truth is queried by the
program. When `zeroClass = none`, the greatest class has nonzero integer
`leading`; no full sum over other classes is needed in the sign proof.

For each actual current item, the literal stage `preimage` is admitted and
has its entire domain on `sourceTail`. Its leader is exactly Phi of that
preimage. For a counter this follows from the checked original scheduled
counter leader-word calibration; for Phi/V/X it follows from literal Phi
projection or checked positive-depth predecessor factorization. Arbitrary
unused letter fields are retained. A current selected-maximum occurrence
exists by `hasMaximum`, with nonzero coefficient from canonicalization.
Its own preimage gives raw maximum <= preimage + its offset. No removed
occurrence or stale variable label supplies that inequality.

On `signTail`, every current preimage reaches
`K = 64*(S+A+A*M+B+1)`, where S is the current nonlinear coefficient mass,
A the current raw-linear mass, M the sum of current preimage offsets and B
the absolute current constant. Let u be the greatest preimage and P=Phi u.
Actual Phi strict monotonicity orders all the other preimages. Hence every
raw variable is <= u+M, and the exact raw-linear/constant remainder has
absolute bound `2*A*(u+M)+2*B` after doubling.

For each actual counter the checked original expansion and residual bounds
give `0 <= 2*E-H <= 2*preimage+2`; ordinary atoms have correction zero. Thus
the full weighted correction is bounded by `2*S*(u+1)`. This uses the
source residual bound on the actual reached interior input, not just the
weaker rational half/three-quarter estimate.

Let Q be the maximum strictly smaller leader, or zero if none. If it exists,
its preimage v is >= K >= 16*S, and v+1 <= u. The checked multiplicative Phi
step gap gives `16*S*Q < P`; in the empty case the same strict inequality
follows from positivity of P. All lower leader terms have absolute sum at
most `2*S*Q`. The checked quadratic gap gives `u*u < P`.

The literal payment proves
`2*S*Q + 2*S*(u+1) + 2*A*(u+M) + 2*B < P`.
Consequently the doubled original row differs from `leading*P` by less than
P. Since `leading` is a nonzero integer, its sign is the exact sign tag
emitted by the stage. Integer doubling is used only in this proof, never
in the emitted exact row replacements.

Authored candidate modules `AlgorithmSignArithmeticProof` and
`AlgorithmSignItemProof` record the numeric error bound and the actual
current-occurrence source/preimage/correction facts. They are uncompiled;
whole terminal sign and full-stage assembly remain pending.

# Checked dominance reuse selected during source review

The actual implementation can use the already accepted generic theorem
`PlainPhiDominanceProof.collected_sign`, rather than reconstructing the Q
maximum argument. New proof-only `numericLeaderData` records each actual
current preimage with coefficient `a*(counter ? 1 : 2)`; the checked
`CommonHeadCollectedRow` collector preserves exact weighted evaluation,
provenance, pairwise distinct inputs and the coefficient mass budget.
Its collected mass is <= 2*S. The actual source remainder has bound
`(2*S+2*A)*u + (2*S+2*A*M+2*B)` from the same counter correction and current
raw-input arguments above. The accepted generic theorem therefore needs
only `6*S+2*A+2*A*M+2*B+1 <= u`, which the frozen 64-payment already pays.
The static extra local source closure is seven modules, three missing local
oleans at review time. This introduces no runtime word evaluation or new
assumed supplier. `AlgorithmSignDataProof.actual_collected_sign` is authored
against the literal source data; it remains an uncompiled candidate. The
remaining terminal bridge identifies the actual final numeric class with
its collected coefficient and derives raw maximum provenance on the region.
