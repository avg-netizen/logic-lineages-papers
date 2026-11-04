# Standard-N semantic least sets and disjoint combination

Paper06 lines564–571 introduces separate positive inductive operators and their disjoint-tag combination. This component constructs only their metatheoretic semantics in Lean: the actual Positive body, evaluated in standard Nat at a fixed encoded context, yields a monotone endomap on Set Nat. The accepted full powerset complete lattice and OrderHom.lfp give its least fixed set.

Targets establish exact unfolding, inclusion in every pre-fixed set, and equality of even/odd slices of the combined least set with the separate least sets. The latter must be derived from actual syntax branch isolation and tag partition, not assumed.

The complete powerset construction needs no well-foundedness of R/DM and makes no assertion that all typed terms belong. It is not an ID1 internal derivation, formal closure/leastness axiom scheme, proof-theoretic ordinal construction, accessibility or well-foundedness theorem. No transfinite-iteration bound is claimed.
