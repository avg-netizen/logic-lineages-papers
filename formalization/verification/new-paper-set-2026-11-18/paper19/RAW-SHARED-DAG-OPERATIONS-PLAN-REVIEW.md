# Raw shared-DAG operations conceptual review

Approved staged direction after reading actual ScopedDAG append/rename/application/eraser/aggregate and GroundEquivalence insertion/reference definitions. This conceptual review does not replace the separate exact structural-action comparator review.

Append order is correctly encodeGraph b ++ encodeGraph a for append a b; Ref.front leaves an index unchanged and Ref.back shifts by the literal front length. The typed renaming table must enumerate every source-context position, with its actual type-preserving target index. Local-prefix positions remain fixed; only free-context positions are mapped with prefix-length offset. No injectivity of renaming should be added, since arbitrary typed renamings may identify variables. Repeated references and unused vertices must remain literal.

Insertion appends ground to each local prefix and shifts precisely free-context variable indices; all graph reference indices remain unchanged under Ref.map. Exact all-constructor graph equalities and table lengths, together with genuine total structural PR programs, are the right first packet. Document malformed tag/payload behavior separately from typed validity; default lookup cannot establish a typed correspondence on invalid renaming tables.

For later checked compositions preserve context/type compatibility and root specifications, not only successful input validation individually. Application shifts the first root by the second table length. Eraser additionally inserts local ground and adds lambda/application vertices, including the final reference shift. Literal aggregate order and empty zero-pair must be calibrated. All rejected incompatible/malformed inputs must follow the defined Option behavior.

Whole all-sort/Boolean/Program/input compiler reconstruction and joint computability remain distinct. Transport existing polynomial actual source-table bounds only after exact reconstruction. No expanded-term proxy, inert sort, implicit normalized-input restriction or added polynomial serialized-bit claim is approved.
