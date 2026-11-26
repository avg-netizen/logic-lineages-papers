# Actual local list-return content inversion

Both targets were frozen before their proofs, separately for cons and nil.

- `OriginalListReturnContentStatementChecks.actualConsContent` was checked in
  bounded build `1794503755996711234-5`. Given an actual supported list-cons
  return and the literal completed result partition, it recovers the actual
  output head's `returnArgumentsCons` graph at the two stored child results,
  and proves that both work and the old result suffix were restored.
- `OriginalNilReturnContentStatementChecks.actualNilContent` was checked in
  bounded build `1794503828221551941-5`. At the corresponding nil-list boundary,
  deletion results are consumed, the actual returned head is zero, and both
  work and the old result suffix are restored.

Neither theorem assumes the desired returned value graph or the restoration
identities it concludes. Candidate values/states are obtained through actual
Program totality and identified with the observed transition by functionality.
The literal completed partition, original control/metadata selectors, and an
actual output pair/cons decomposition remain explicit inputs. These are local
boundary laws, not a proof that a whole execution reaches the required boundary
with semantically correct child/deletion observations.

The source files contain no `sorry`, `admit`, added axioms, `native_decide`,
unsafe declarations, or raised checker options. The bounded checker enforces
the existing allowed axiom policy. Frozen target hashes were rechecked unchanged.
