# Exact encoded polynomial undecidability

Native target-only preflight: 1793880669245927168-2. First native exact gate:
1793880747702394216-2. Three aliases passed with only propext, Classical.choice
and Quot.sound. All 74 local imports match successful source-bound native
receipt rows. Original targets and supplier bytes remain frozen. Independent
review/adoption is pending; no downstream or whole-paper promotion is asserted.

The witness predicate is actual halting on input zero, expressed on natural
code indices: Dom(eval(ofNatCode e) 0). Its RE proof uses the proved partial
recursiveness of eval and computable code decoding. Its undecidability pulls a
hypothetical Nat decider back through computable ordinary-code encoding and
uses the proved encode/ofNat inverse to contradict Mathlib halting_problem 0.
The co-RE/complement theorem halting_problem_not_re is not used.

The original checked REPolynomialReduction supplies a computable reduction of
this RE predicate to the unchanged encodedPolynomialSolvable predicate. A
hypothetical decider for that predicate composes with the reduction to give the
forbidden halting decider. The final alias is exactly the original
Targets.EncodedPolynomialUndecidable, with no unproved supplier premise.

Polynomial semantics retain actual integer coefficients, natural roots
including zero, original canonical encoding and malformed-code rejection.
No algorithm choosing finite representations from arbitrary extensional proofs
is inferred. FunctionalHardnessCompletion.encodedPolynomialSolvable is a DIFFERENT language:
linear simultaneous systems over unknown N[X] polynomials. The four comparison
reductions start from that language. An effective Narendran-style bridge from
the integer-polynomial/Nat-root language proved undecidable here is still
required; identical short names do not identify the predicates. Downstream
undecidability therefore needs that bridge, exact gates and independent review.
