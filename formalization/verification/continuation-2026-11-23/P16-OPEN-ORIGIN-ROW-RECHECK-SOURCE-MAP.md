# Paper 16: recheck the same inserted row in the allocated removed side

Paper 16, `sections/ordinals.tex`, lines 143–153. An original
`InsertedRowCases` report supplies the literal tag-4 row equality,
three original selector reports and original positive certificate graph.
Given a physical parse of a new side's removed tape and genuine
`scratchMember` acceptance at the same original dominator key, the
reconstructed graph is an accepting run of the very same
`insertedRow r` checker. The code of the row, decoded target and
dominator and positive certificate remain unchanged; only the pool
parameter changes. The proof uses object-calculus graph composition
and accepted branches, not numeric reflection.

Exact gate `LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowRecheckProof`,
alias `exact_OpenRecheckOriginRow`. It does not choose a side or prove
that one of the side membership tests accepts; that requires the
actual source-origin count and append law.

Frozen Lean source hashes (SHA-256):

    9b432e0a30016ea4885b6c451d95fef6e7309de5603faffad830fee31c73c98f  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalOriginRowRecheckProof.lean
    b22235058bc3b51c7eebcc0566315bb86ce4bf9eaa065ed6d07be8bb1a782551  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalOriginRowRecheckTargets.lean
