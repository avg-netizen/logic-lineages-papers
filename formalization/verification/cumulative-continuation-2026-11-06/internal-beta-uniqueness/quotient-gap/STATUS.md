# Internal quotient-gap arithmetic supplier

Passed: frozen arbitrary-context first-argument multiplication distributivity, and the exact original four-equation quotient-gap contradiction. Both exact aliases depend only on `propext` and `Quot.sound`. This supplies arithmetic for beta uniqueness; it is not itself beta uniqueness or a numbered paper completion.

The first target candidate failed only namespace ambiguity and bottom notation. Its source, hash and compiler receipt are retained. Corrected target hash was frozen and the target passed before proof compilation. The initial proof candidate was written while the first target check completed; it was not compiled until the corrected target passed. There was no mathematical target weakening. First proof compilation passed without repair.

Proof uses original PA induction for left distributivity, original left-successor multiplication, additive associativity/commutativity, and original `noLoop`; no semantic reflection premise. Peak proof process-tree RSS: 1,192,136 KiB. Checks used pinned Lean 4.32.0-rc1, 2048 MiB heap, 1536 MiB RSS cap, 2048 MiB free floor, one thread.

The parent InternalBetaUniquenessTargets module also passed, receipt 1793999543823683797-5.json. Compiler released. No commits, full-root checks or publication.
