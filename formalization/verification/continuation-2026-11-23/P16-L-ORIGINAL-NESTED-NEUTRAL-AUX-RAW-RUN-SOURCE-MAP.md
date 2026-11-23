# Paper 16 (L): original numeric nested auxiliary raw run and direct step

On input outer aux [D,C,inner aux [d,t,bare atom,a],b], the actual
original raw run either supplies a whole bottom root with its
literal witness wrapper, or keeps the exact outer right argument b
and supplies a literal tag5 wrapper with explicit child raw witness.
The latter is verified by the actual residual run at one fewer outer
tick and the literal inner AuxStepShape proof. This gives either
outer aux of bottom t or outer aux of the same inner row now headed
by bottom stored (a free head only), with the corresponding witness
parses. The direct step conclusion adds original admission of y at
the original context/request. No alternate checker is used; canonical
right-argument exchange, arbitrary-depth induction and object closure
remain separate. The previously private exact one-aux raw-run proof
is restated locally so its arbitrary residual fuel can be consumed
without modifying the established one-aux source.

Gate NumberedWindowNeutralApplicationReductionRunProof;
exact_OriginalNestedAuxRun and exact_OriginalNestedAuxStep. Native pending.

Frozen Lean SHA-256:
    bb03a4f187555aaec3e1a775c478d62f26433686777f42b7dbb8251e403bdd03  formalization/LogicLineages/PersistentMarking/NumberedWindowNeutralApplicationReductionRunProof.lean
