# Independent review: constructor-first protected-spine dependency plan

## Decision

Approved as the source-compatible dependency design for authoring exact definitions and a frozen comparator, not as proof acceptance. Reviewed PROTECTED-SPINE-CONSTRUCTOR-DEPENDENCY-PLAN.md against decision.tex 41–65, 81–98, 108–163 and ordering.tex 28–38, 48–56, 59–95. No mathematical source or accepted target is changed. The rejected direct-M interpreter must stay outside the module tree.

## Why this repairs the sequencing defect

Decision.tex 112–130 specifies a newly computed marked value, not the arbitrary old family entry. Its observation tests inspect previous-approximation premises; its nonempty table appends the entire tuple and consults the previous family. The new builder can therefore precede source recursion: it reads finite target syntax, actual base/extra values, existing complete table actions and old M, never its own output or the interpreter. In particular FAbs must inspect old M at the extended owner, not recursively construct a new marked value. This is consistent with the previous-approximation requirement at lines 126–130.

A concrete marked image interpreted by this builder then has the same full-table append/old-M behavior as the original-head helper. No arbitrary-M append law, fixedpoint premise, semantic name-equivariance or staged application identity is needed or approved. Ordinary-head full tables must likewise follow lines 132–134 literally; their observation fields use the constructed marked counterpart rather than replacing it by old M.

## Exact constraints for the next freeze

1. Select retains all typed suffix decompositions. Ordering.tex 30 permits the empty call; decision.tex 46 has tables only for nonempty prefixes. Thus the empty Select branch must read the selected value itself, while a nonempty branch uses exactly one full action. Retyped arguments are old-M values of the same head/base/extras, in the literal domain order. Derive all domain/residual types, retained outputs and tuple success internally from actual inventory and action contracts.
2. Stat keeps base positions and multiplicities. Its witness must encode both occurrence partitions, a typed weak bijection on retained occurrences, a nonempty removed source set and a strict source witness for every added target occurrence. Removed source occurrences may cover zero or several added occurrences. Extras do not enter this multiset test. Copy/Stat additionally retain every retyped whole-owner weak premise.
3. FAbs chooses the port solely at the actual descendant observation coordinate. Both weakening paths must use that same coordinate/choice and actual restriction composition. Derive the spare slot, permitted type, opened observation membership, insertion validity and old-M output success; no caller freshness/coherence oracle and no comparison of distinct opening choices at fixed arbitrary M.
4. Builder tables return actual old-M outputs after simultaneous full-list insertion. Before encoding, prove hereditary output membership, tuple monotonicity and naturality, including all contexts and all prefixes. Availability and both observation fields must match the stated builder, not merely be observationally equivalent at the root. The actual input/M monotonicity and family (C) proofs must cover Select and FAbs as well as table fields; finite positive tests alone are not those proofs.
5. Raw ill-typed branches may have explicit conventions, but prove them unreachable for every valid parameter/coordinate. Optional lookup or encoding failure cannot silently select a valid-case bottom. Encoding must follow validity, and family encoding must follow all-parameter monotonicity/coherence.
6. The subsequent Expr/Args/nonempty-helper recursion must exhibit an actual well-founded measure for every cross-call. No call recurses on a substitution image, retyped owner, new family iterate or same-source empty helper. Empty residual interpretation resets call-local protection; later independent calls start a fresh scan. Definitions must not obtain this behavior from an unproved substitution or helper-correspondence theorem.

## Still unpaid

Exact builder code and all laws; structural source/helper validity, monotonicity, weakening, capture-avoiding substitution and concrete full-application correspondence; the actual source-universe/fresh-port obligations; canonical-child derivation transport and uniform smaller-derivation IH for adequacy; the concrete operator and stabilization. The earlier canonical-coordinate review remains in force. This approval does not establish the printed structural-interpretation lemma or an arbitrary-M opening-independence theorem.

No native/compiler invocation was performed for this review.
