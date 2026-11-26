# Source map: actual sparse pairing decoder inside arithmetic

Paper 16 `sections/ordinals.tex` 12–29 and 70–76 uses literal finite typed syntax
and genuine numerical certificates for the finite quotients and positive
paths. Lines 84–98 and 112–127 require arithmetic predicates and use
function-side path mirroring. The selected current repository representation
`NumberedWindowPairAlgorithm` is the sparse polynomial `(x+y)^2+x` with
the original bounded optional search, not Mathlib `Nat.pair`.

The new literal ASTs use the original arithmetic compiler and its existing
natural-number operations. If the code is n, take s=floor(sqrt(n)),
a=n-s*s and b=s-a. Reject precisely when s<a; otherwise choose (a,b).
The malformed/nonimage case remains an explicit rejection. There is no
restriction of the external domain to generated codes and no replacement
of the original pair, order of fields, or bounded-search definition.

`CandidateValues` and `GuardValue` state the literal selected programs'
all-input evaluation. `AllInputDecoder` states complete optional equality
to the existing bounded search. `OpenSuccess` states actual proof trees in
the same finitary language for the relation between original polynomial
pair construction and a successful selected decoder with both coordinates.
`OpenFailure` retains both directions: output zero is proven equivalent to
no original polynomial preimage, with two genuine object existentials and
arbitrary free terms. The paper uses codes, not a proof oracle, and neither
external natural truth nor an external computability theorem is a rule.

The proof plan uses the retained, actual floor-root interval and arithmetic
subtraction diagonal plus functionality, deriving weak-order difference
witnesses in the original calculus. It does not use the old max-square
pair or unpair result to identify either coordinate. The reusable weak-order
witness statement itself does not mention any encoding.

This split success/coordinate representation supplies a calibrated staged
decoder interface. It does not silently substitute a new AST for an accepted
optional-code parser or for a previous `sourceBody`. A later ordered-list
and tagged-node packet must apply these graphs in its own consistently chosen
syntax and prove a new all-input calibration. No path lift, full matching,
or numbered ID1 accessibility proof follows here.
