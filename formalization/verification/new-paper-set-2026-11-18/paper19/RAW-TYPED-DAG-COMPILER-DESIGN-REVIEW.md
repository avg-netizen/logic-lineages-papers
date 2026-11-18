# Raw typed DAG compiler conceptual review

Approved staged direction to an exact first codec freeze, not full compiler acceptance. Read design and actual SourceGroundEquivalenceDefinitions: all seven DAG node constructors, dependent spec list, binder prefix and Ref indices must be preserved. The actual Input root has spec ([],tau). Exact typed reconstruction, including graph and root and repeated references, is stronger and necessary here than equality of expanded terms.

Freeze concrete raw layouts and reject extra payloads as well as bad tags/types/references. Oldest-first raw node order versus newest-first typed spec list must be calibrated explicitly at every extension. Lam must check sigma::Delta against the earlier child; variable lookup uses Delta++Gamma. Arbitrary internal types, case and recursor must remain accepted. Sharing/node count must refer to actual table vertices, not term expansion.

A total Computable raw validator/normalizer plus deterministic unique typed reification may be a workable staged interface, but normalization alone is not enough to claim an effective decoder: the finite typed construction and its exact successful graph/root correspondence must be derived. Do not introduce a choice-based decoding oracle. State precisely whether noncanonical syntactically valid raw codes are accepted or rejected; primary typed roundtrip and rejection behavior cannot depend on an implicit convention.

Subsequent raw operations, all-gate sort forest, whole interleaved Input normalization and output reconstruction remain unpaid. Legacy unsupported tag5 and unfolded leaf terms cannot cover those debts. No polynomial encoded-bit complexity requirement is added; actual source-DAG size and genuine joint computability remain the source requirements.
