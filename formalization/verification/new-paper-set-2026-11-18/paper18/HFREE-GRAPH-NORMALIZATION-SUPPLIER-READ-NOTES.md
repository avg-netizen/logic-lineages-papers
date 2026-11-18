# Independent supplier mathematical read, in progress

Not a final acceptance. No native launched. Read ExpandedGraphDefinitions/LocalProof, RealizationProof/Helpers/FrameProof, UniquenessProof; previously read BooleanGraphSemanticProof, initializer semantics and fresh packet proof/calibration/program candidates. Read initializer class proof in this pass.

Local subtraction divides x<=y (z0) and x>y (x=y+z), matching Nat truncation. Division0 explicitly z0; positive division uses cz<=x<c(z+1) and real Nat.div_eq_iff. Inverse supplies u=z+1 plus (z0 or Phi(z)<=x) and x<Phi(u), matching actual SnyatkovInverse graph including below-range0, not an arbitrary inverse oracle.

Total realization is actual finite postorder updates. Unary/binary helpers derive child freshness, disjoint allocated intervals and frame preservation; earlier child graph is unchanged by later updates. Source values are unchanged because original names lie below allocation start. Phi inverse separately updates u to v+1 then output z to v, proves both slots distinct/from child, and preserves all original names. H/hyperInverse are rejected by explicit H-free admission. Allocated uniqueness splits child intervals/output and in inverse also derives successor auxiliary uniqueness; not merely output uniqueness.

Boolean graph semantics keeps a total forest outside predicates and transports original valuation by the frame theorem. Negation uses not_congr under the same graph; disjunction/conjunction build both graphs with shifted allocations. Divisibility0 is equality, positive modulus uses exact encoding. Initializer semantics is uniform signed arithmetic, including zero/negative coefficients, then structural Boolean recursion and exact existential prefix updates. Its class proof retains only variable/unshifted Phi bound occurrences; free terms remain parameters and output H-free is constructor-derived.

Still required before final: full evidence, source/freeze identity; complete support/allocation/class and concrete raw graph/initializer program closure review as warranted. No PlainBlock solver, elimination or arbitrary-alternation decision acceptance from this pass.
