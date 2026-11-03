# Numeric annotated scalar data foundation

Paper09 source-realization.tex93–109 and128–175 retain actual operator annotations, full ground-abstraction copying, and ground-binder transport; effective use192–226 needs literal numeric operations.

The codec stores each actual raw operator's arity, original source code, and COMPLETE ordered vector-code list. It never compresses to a head-only record. Scalar Tree code distinguishes free/tracked/add/collapse and retains repeated occurrences. The erasure numeric fold takes an explicit tracked deBruijn index and retrieves head coordinate1 only for the erased collapse, while preserving the full stored payload in the tree code.

ExactOperatorCodec calibrates all stored fields and head extraction, including required in-bounds coordinate1. ExactErasure covers all typed Tree values, without Valid. ExactRepeat covers all counts, including zero and exact literal repeated tree shape. ExactClosing separately proves whole operator payload source-head deletion/full-vector headClosure, then the entire literal tree close operation. Arbitrary internal source binders are handled by SourceCarrierMapCode's already paid actual typed map; tracked Tree symbol remains symbolic under the closed context. All four numeric transforms are primitive recursive with no supplied operation oracle. Malformed payloads use explicit empty-list defaults and total fold branches; no malformed validity claim.

Scope is numeric annotation data foundation only. Numeric ground partial, raw original source annotation builder, numeric accounting and exact whole K map remain pending. Existing typed/data semantic construction is not relabeled full effective theorem.
