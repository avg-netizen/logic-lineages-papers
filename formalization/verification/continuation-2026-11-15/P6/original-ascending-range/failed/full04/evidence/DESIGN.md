# Original ascending range prerequisite (exact2)

Original source: NumberedCodeEnumerationPrimrecSupportProof, NumberedAuxiliaryEnumeration.layer, lines31 and36. Variable constructors use List.range variableBound; numbered labels use List.range(labels+1). Both require the ascending occurrence order, not just finite-set membership.

Concrete AST: range = Nat recursion with zero-arity constant0 base and step(index,previous) = append(previous,consCode(index,0)). Original successor/pair list codec, original append, original Nat recursion; no opaque supplier and no new encoding. Zero bound gives []; successor appends the single index at the right. No duplicate removal or sorting. List.range itself has no duplicates, but the append implementation does not filter occurrences.

NativeRange calibrates to the actual Encodable List Nat instance, not a silently substituted custom list encoding. Codec identity is an internal proof duty. Every Nat is a valid bound. Thus there is no malformed-bound decoder or default[] branch to invent. On arbitrary intermediate previous-list codes the literal original append raw-list semantics are retained, including its existing defaults; no native-list image is assumed in the internal target.

InternalMembership quantifies actual graph output out and arbitrary raw index and bound. It requires only the actual range graph, deriving both membership-to-strict-bound and strict-bound-to-membership internally. It must pay base impossibility, successor append membership split, singleton membership/equality transport, and discrete-order successor split internally. No length, decoded image, validity, rank or range-membership premise is added.

Duplicate check: searched ID1Completion range-named modules and List.range in Definitions files. Existing hits are Boolean range contracts, native context findIdx, and native hereditary-row specifications, not an explicit calibrated ascending list Program with internal membership equivalence. Original numbered source has Primrec existence for range but no concrete Program of this contract.

Remaining: the eight-block full constructor-layer append assembly, opened variableBound+1/fuel recursion, full enumerator calibration/completeness, and Q are unpaid. The accepted corrected numbered branch and TypeLists are distinct existing prerequisites. The old false raw-head numbered native packet remains blocked unchanged. This packet does not install a full supplier or claim whole E/Q completion.

Proof plan only (not authored): native Nat induction and original Nat/list codec identities; internal ordinary induction over bound, recovering actual recursion/append/singleton outputs and using existing append membership plus arithmetic strict-successor laws. No native reflection, new axiom, heartbeat increase, or checker change.
