# Separate generic-control actual ordinal collapse

Paper09 hardness.tex lines267–277 invokes the collapse construction with its new control Gamma_b. Existing actualCollapse and WWOrdinalTermSemantics.denote are fixed to Phi. This supporting component constructs a separate collapseWith G on actual ordinals by the same well-founded recursion over actual norm-bounded predecessors, with G replacing only the numerical budget function. No accepted implementation or semantics is edited.

ExactRecursion proves both the defining finite maximum equality and an independent universal upper-bound/least-upper-bound characterization for every G, below epsilon zero. UniqueBelowEpsilonZero proves uniqueness from that independent equation, without monotonicity or an assumed recursive solver. ExactPhiSpecialization calibrates the separate implementation to accepted actualCollapse at G=Phi on the genuine domain. FiniteValues proves collapseWith G(n)=n assuming only the explicit identity-majorization n≤G(n) for all naturals. The off-domain zero branch is totalization only.

Dependencies: actual finite norm balls and bounded predecessor membership, actual ordinal well-foundedness, actual norm on naturals and epsilon-zero closure; accepted actualCollapse equation/uniqueness. No computability claim for arbitrary G is made.

The coefficient-one formula, Gamma instantiation and parameterized literal source denotation/gadget semantics are separate pending steps. In particular no equality of collapseWith Gamma and actualCollapse is claimed, and no old source gadget is silently reused at the new control. Full paper09 hardness remains pending.
