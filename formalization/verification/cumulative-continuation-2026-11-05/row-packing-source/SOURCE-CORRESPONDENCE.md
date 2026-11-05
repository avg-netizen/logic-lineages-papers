# Variable-length elementary witness-row packing

All four frozen targets passed the bounded native gate and standard-axiom
audit, after target-only preflight. See `ROW-PACKING-ACCEPTANCE.json`.
This is a six-file package: exact semantic packing and its actual Diophantine
graph for a variable row length. It is not merely fixed finite conjunction.

## Verified scope

- Under an actual valid row code, source Const is equivalent to that row being
  pointwise constant.
- The six elementary cases preserve semantics under valid witness/index rows:
  natural constant, witness copy, index parameter, other original parameter,
  addition and multiplication.
- For every fixed finite elementary system and every original parameter
  valuation, pointwise existential witnesses for each i<len exist iff the
  system has a packed cipher representation with one common q.
- The relation forall i<len, exists finite natural witnesses, all elementary
  constraints hold is genuinely Diophantine, with len as a free input.

Original parameters, length0, empty witness blocks and empty equation families
are retained. The forward proof chooses witnesses on Fin len, takes the finite
maximum over Fin len × Fin k, chooses q=len+maximum+2, and encodes actual rows.
The reverse proof decodes actual functions from valid cipher witnesses.
Source Const and Mult retain their previously checked distinct empty behavior.

The graph proof uses only checked cipher/index relations and existing finite
composition, conjunction and existential projection. No variable bounded-
universal premise or new oracle appears.

## Primary-source correspondence

https://github.com/uds-psl/H10-LMCS-v1.1/blob/c2586aee45cf60e7fb8b112ac701b02d7dc3cfeb/theories/H10/Dio/dio_bounded.v

- Lines 78–85: six elementary constraint cases.
- Lines 203–217: valid witness rows and actual index row.
- Lines 239–318: variable-length packing equivalence.
- Line 321: pointwise elementary-system Diophantinity.

No Coq theorem is imported as a Lean axiom.

## Remaining boundary

The original full VariableBoundedUniversalClosure target still needs assembly:
transport the checked natural normalizer to Option(Fin n), apply this packed
pointwise theorem, and substitute the original Diophantine bound function.
Ordinary recursion/minimization graphs, universal evaluation, computable
polynomial specialization, RE reductions and genuine MRDP remain pending.
