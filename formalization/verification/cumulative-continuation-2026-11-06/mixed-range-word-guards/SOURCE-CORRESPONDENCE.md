# Arbitrary-gap source mixed-rank comparison and stripping

Baseline: `a434702566f4aef164141d3b5a2f3ce338a350f2`. Every tracked baseline source, manuscript, target, checker/dependency file and register remains preserved.

## Exact source cases

- Paper08 lines 275–300 and 603–608 expand only the higher source head until its outer rank matches the opposite head. The accepted finite exposure prefix is retained at the original interior input; its final exposed head is immediately compared and stripped.
- `MixedKernelGuard` covers every pair r>s>=3: s=n+3 and r=n+m+4. Its retained word is the original A followed by the literal descending prefix for those ranks. It invokes the unchanged shifted equal-rank source guard, retaining input, reverse mass, signed depth and exact outer-shift ties.
- `MixedQuadraticGuard` covers every r>=3 against literal V: r=m+3. Its exposed index is exactly j-ceil(c/2), with no rank-two X emitted. The opposite V index k remains arbitrary, including negative indices and exact ties.
- At m=0 both targets reduce to the accepted adjacent-rank shapes. No special gap assumption is hidden in the arbitrary natural m.
- Lines 559–572 and 584–602 require literal structural inputs and signed domains. Each cutoff pays the actual finite-exposure context and the complete same-rank guard on the retained left word. Original A(x)/B(y), both full original domains, and generated retained-word admission/domain are preserved.

## Exact local rank effect

The local identity in `MixedHeadDecrease` matches lines 614–625. After immediate comparison and stripping:

- E count is unchanged.
- One opposite exposed-rank occurrence is deleted.
- The original highest-rank occurrence is retained.
- Exactly one occurrence is added at each strictly intermediate rank.
- All other rank counts are unchanged.

The proof computes the count of every retained rank, not only a rank bound. The first changed range rank therefore decreases, while higher-rank counts may grow as the paper allows. This is a local vector identity, not a complete well-founded recursion theorem.

## Source semantics and effectiveness

Exact original-source calibration, parent/inner/child bridge thresholds, signed positivity and the quadratic endpoint are inherited from unchanged finite exposure and one-step source expansion. No companion schedule substitution, inverse counter or independent interior witness is introduced.

The actual retained-prefix append and both finite-gap cutoffs are uniformly primitive recursive in the two words, rank gap, masses, signed depth indices and outer shifts.

## Boundary

This completes the stated mixed ordinary-head comparison cases as supporting suppliers. It does not construct the full recursive guard compiler, prove global termination, handle terminal leaf/nonlinear growth, preserve row-cancellation provenance, or establish closed existential decision. No numbered source theorem is promoted. Register remains 167 checked, 2 inherited, 20 pending / 189.
