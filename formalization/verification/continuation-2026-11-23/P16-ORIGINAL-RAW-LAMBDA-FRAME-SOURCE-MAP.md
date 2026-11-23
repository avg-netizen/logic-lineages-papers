# P16 exact sparse lambda-body frame

Paper 16 `sections/ordinals.tex:132–138`: a direct lambda-application
reduct can reduce the body on the function side. This packet cuts out the
physical **lambda context frame** used under that function step; it does
not assert the whole resulting positive path or inherited computability.

Literal source: `NumberedWindowRawContextAlgorithm.context`'s original
tag 1 + singleton child witness case; endpoints both tag 2 with ordered
[stored domain, body]. The stored domains must coincide. The output is
the exact ordered triple [source body, same actual child witness, target
body]; `tagOneNext` first checks the original witness decoder.
A malformed node, wrong tag/arity or different stored domains is
rejected. A success is successor-packed, even if one actual field is
zero. The child witness arithmetic context is not replaced. The outer
raw tick has false intermediate status, regardless of root callback or
previous status, and the actual emitted frame.

* Targets define a separate narrow physical Program, reusing exact
  `onRaw/field/sameSlot/consOf` from the tag-five frame; they do not
  edit the original runner or assert equality to its whole program.
* NumericASTProof follows the original same-domain check and exact
  branch result on the actual [source,witness,target] tape.
* NumericProof gates all-input equivalence to the restricted original
  `next 1 [child]` and actual original literal raw tick.
* OpenProof supplies actual symbolic original node parse selectors, the
  same stored domain's actual equality, and the unchanged physical
  body's and child witness's selected fields in the exact emitted
  frame. It works in arbitrary open object contexts.

No old opaque positive or least program is reflected. The packet
does not claim a typed body step, installation into the root runner,
typed transport through substitution, raw path/least completeness,
or lambda computability. These are distinct follow-on obligations.

| Module suffix, prefix NumberedWindowInternalSparseRawLambdaFrame | SHA-256 |
|---|---|
| Targets | `f5394fc5540ffe508ed2c56f0a730d46e2c19668df58bb585c775e07810d88b0` |
| NumericASTProof | `6360ed2ae7a8a22cbc86264173f468fece7305639928a395da18d445feae8d4c` |
| NumericProof | `2f611aba057d69794252f12943e0846adcc19d35127299d2c7e516e676bbe7e0` |
| OpenProof | `212bbee455a64e958db6ca6daad7f3c43f17a31935dc395392eef294ff6a4d1c` |

Gate NumericASTProof then NumericProof; OpenProof is independent of
numeric proofs. Report only exact kernel-checked aliases.
