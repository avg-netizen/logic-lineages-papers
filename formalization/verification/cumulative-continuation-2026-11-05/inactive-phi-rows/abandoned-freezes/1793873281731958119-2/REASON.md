# Abandoned comparator freeze

The ActualInactiveAtom clause omitted parentheses around its
conditional equivalence. Lean parsed the source as `(inactive → output) ↔ input`,
which is not the intended source theorem and is not claimed proved. The author
check exposed this at receipt 1793873625676549133-2. The other five targets and
definitions are unchanged. Corrected target-only preflight is required before
restoring or reauthoring candidates against the intended statement.
