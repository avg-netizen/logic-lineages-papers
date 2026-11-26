# Paper 16: actual scratch minimum and numerical packed least composition

## Original source and separate numeric contracts

`16-persistent-marking-termination-ordering/sections/ordinals.tex` 70–77
uses the original primary quotient and optional least-code representative.
The source functions here stay literal: `NumberedWindowClassAlgorithm.least`
is `List.min?` of original `members`; `members` takes the original
`rounds` at the length of the unchanged input vertices. The original
`NumberedWindowScalarAlgorithm.least s g ty seed` supplies
`edge s g ty` and `vertices s seed`, with **g an already decoded list**.
The packed API frozen earlier in `NumberedWindowInternalSparsePathAdvanceTargets`
instead takes a packed context c and binds the one original
`NumberedWindowFieldAlgorithm.unpack c` before calling that function.
The API applies `encodeState` to the result (none→0, some k→k+1).

`ExactAllInputScratchMinimum` directly calibrates the actual unchanged
`NumberedWindowInternalSparseOrderedMinimum.scratchMinimum` on every code
of the **standard Nat.pair scratch representation**, against
`encodeState (((decodeNumbers code).getD []).min?)`. The physical recursor
has nil zero and the original exact optional update `minimumStep`;
minimum zero is a successful 1, not a failed 0. `decoderTotality` ensures
every standard scratch natural decodes. The explicit option fallback is
retained and is not a claim that a malformed sparse field decodes. Original
#727 has a public exact sparse raw wrapper, but its scratch-list theorem
is private. The direct standard-scratch proof is still new here; its
source-exact suppliers are original listRec numeric evaluation, the
public #727 `stepValue`, and the literal `List.min?_cons` law.

## Actual physical packed composition on [ctx,ty,seed]

- `contextOption` calls the existing original sparse `parser` on
  projection 0. Accepted #628 gives its exact all-raw numeric output
  `encodeResult (unpack ctx)`, zero on malformed input and a successor
  even when the actual successful ordered context is empty. It is the
  **actual Option tag**, not the payload after predecessor, that is tested.
  `AddressAlgorithm.contextView` has an additional `all typeBit` guard and
  is not this original packed API. The legacy `Encodable.decode ... .getD []`
  would incorrectly confuse absent and valid empty context here.
- `poolAtSeed C s` feeds projection 2 to the actual fixed cover-to-scratch
  producer with the same selected Program3 C; its exact original fixed
  head/type constants and original cover Option are retained in that
  producer. The scratch result is the exact ordered `vertices s seed`
  encoding, including any repeats and only the original fallback.
- `membersAtSeed C X W s` passes that actual pool and unchanged runtime
  projections [0,1,2] for packed ctx, ty and seed to actual `members`.
  The latter computes length from that very pool and uses the same actual
  ordered pass at each successor. Its edge is **one physical `edge4 X W`**,
  with original term X and the same W guard at both directed endpoints on
  the same packed context/ty, accepted numerically in #740. The wrapper
  does not substitute the parser scratch payload for packed ctx, switch
  E at a round, or supply a different pool or fuel.
- Apply the unchanged `scratchMinimum` to those actual member-list bytes.
  `packedLeastProgram C X W s` is the actual original conditional
  `branch contextOption (constantZero 3) minimumAtMembers`. A malformed
  packed context yields zero, regardless of any equality stutter in the
  directed kernel. A valid empty context follows the real successful
  branch, and new seed admission or a new type-code test is not added.

`ExactPackedLeastComposition` keeps explicit the original
`ActualSelectedCoverOutput C` (the #520 whole optional source),
`ActualTermExchange s X`, and unchanged
`ActualPackedWindow s W`. It concludes the existing all-input
`ActualLeastCalibration s` for **that physical program** on the literal
packed tape. In a successful unpack the later proof will specialize #740
conditional calibration to the literal `edge s g ty`, compose the exact
standard-scratch cover projection and original members, and use the exact
standard-scratch minimum. It need not choose another existential edge,
another cover, or another least witness.

## Independent proof prerequisites and scope boundary

The typed target-only preflight does not pay any theorem.
Prior verified supporting inputs: #628 original exact sparse parser,
#727 actual minimum-row numeric source, #739 actual ordered pass, #740
actual packed scalar edge. The separate exact numeric cover-to-scratch
and directed rounds/members results must pass their respective
preflights, exact proof gates and independent review before use. The
old selected packed `leastWitness` is not a proof of the composed AST.
Combining C from the checked cover selection and X/W from #740 for a
concrete callback is a later application; replacement of a previously
installed physical least within raw/path/address/application wrappers
would require genuine reassembly, not numerical graph transport.

Neither target asserts arbitrary-open parser/admission/edge meaning,
filter or round witness propagation, least-self object correctness,
same-presentation installation, original RawMatching, reachability,
or numbered accessibility.
