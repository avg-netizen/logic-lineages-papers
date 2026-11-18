# Derived checked source-DAG operations supporting comparator

Supports compiler.tex's computable construction on actual shared typed source DAGs. This is not complete compiler acceptance.

TypedExactness: exact pair encodings of ScopedDAG.detectorLeft/Right, every same-context typed list's literal right-fold aggregate, and both actual upperInput/lowerInput wrappers selected by Bool. Repeated/unused vertices, exact refs and lexical prefixes retained; empty aggregate produces the literal two one-node zero graphs.

SuccessReconstruction: arbitrary raw successes derive actual same-context ground input witnesses; aggregate derives one typed list whose elementwise encodings are exactly the original list and whose context encoding is the explicit supplied raw context. Every output equals the actual operation's encoded graph and successfully decodes to that graph. No assumed typed input oracle.

RejectionAndCounts: rejection iff the concrete finite guard fails; exact all-raw detector counts 2*(na+nb)+6, aggregate per-side sum(2*(na+nb)+8)+1, upper/lower +6; actual successful output validity. Exact reconstructed outputs carry context/type/root information, not only lengths. All Nat context/type codes are valid types; incompatible codes, nonground inputs, or inconsistent contexts fail guards.

Effective: joint Computable of concrete Option routines on every raw input, including malformed. Guards and right-fold construction are executable; existential witnesses are soundness conclusions only. Computing code never chooses a typed witness.

Literal wrapper order: magnifyRaw uses app :: zero :: lambda :: inserted input; identity/constant use app :: lambda :: locally bound variable/zero :: original input. These match actual definitions and must not be replaced by a denotationally equal eraser shortcut.

Checked renaming, source primitive constructors, real all-sort arithmetic/Boolean/Program codes, complete normalization/input encoding and final computable compiler remain separate. No polynomial encoded-bit time claim is made.
