# Independent pre-scope review: persistent marking

Approved for native preflight as a **supporting raw-syntax component only**.
No numbered Paper16 statement is thereby promoted.

Read the actual foundations and ordering sections and all four candidate Lean
files. Rehashed every source/comparator pin in MARKING-FROZEN.json; all match.

- Native constants are nullary with the printed declarations; the recursor's
  argument order is natural test, step functional, then initial value.
- Application is a binary typed head, not an implicit curried ranked symbol.
- Ranked heads retain arity and ground result. Signature finiteness and name
  admission are deliberately not established in this raw carrier.
- Marked nodes retain original head/base/extras while storing a distinct output
  type. Marking fixes every marked field, follows only the initial lambda spine,
  and is undefined exactly at variable-ended spines.
- Total headmark leaves variable-ended spines unchanged and otherwise agrees
  with partial marking. The frozen persistence, idempotence, agreement, failure,
  and outer-type laws match these literal definitions without new premises.

The representation admits malformed raw annotations, uses names rather than an
alpha quotient, and has no typing judgment. Consequently `TypePreserved` means
preservation of its outer annotation function, not preservation of well-typedness.
This is explicitly disclosed in PLAN.md and the freeze. The laws extend to the
raw superset; they must not be advertised as the full paper's typed relation,
substitution, alpha invariance, structural stability, or lem:elementary.

The proof scripts and exact aliases contain no added axioms/sorry/native_decide.
This review is static; native compilation and actual axiom/evidence reconciliation
are still required. No proof/source file was edited and no compiler was run.
