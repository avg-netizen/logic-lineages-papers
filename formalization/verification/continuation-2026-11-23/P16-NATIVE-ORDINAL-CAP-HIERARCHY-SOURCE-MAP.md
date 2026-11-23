# Paper 16: rank-free actual native cap hierarchy

This is a finite-dimensional extension of the actual cap/successor lower
witness behind the printed height question in `sections/ordinals.tex`. The
construction uses the original terms and the original confined comparison,
without treating that comparison as monotone in an arbitrary argument.

* `NativeOrdinalCapHierarchyBoundsProof` defines a closed typed step at every
  level: level zero is the original native successor and each later level is
  the literal lambda from the separate cap-abstraction proof. A genuine
  native beta step and the checked original arbitrary-step cap theorem give
  `exact_CapLevelIterationCeiling`: every lower-level finite application on
  u is strictly below the next-level application on u. The latter is not
  identified syntactically with the original cap beta target.
* Its dependent `Coordinates` are unit at dimension zero and a highest
  natural coordinate paired with the remaining coordinates at dimension
  successor. `blockAt` applies the highest-level iterations first, from the
  same arbitrary original payload. `exact_CapHierarchyFloorCeiling` proves
  that each block term is at or strictly above the input and strictly below
  the next bounding term. It uses actual strict iteration, not replacement
  of the native order by a numerical ranking function.
* `NativeOrdinalCapHierarchyLexProof` proves literal highest-difference
  lexicographic preservation, reflection and injectivity into original
  `NativeBelow`. The proof separates different highest coordinates by
  actual floor/ceiling and identifies remaining payloads when the highest
  coordinates agree. Reflection and distinctness use actual native
  well-founded asymmetry, not an assumed order on the image. The arbitrary
  well-typed payload includes the original zero term.

No equality with the older two-coordinate syntax is asserted (there the
higher layer was written directly with caps, not the new unapplied
abstraction followed by application). No ordinal library, rank, order-type
calculation, global height, or exact printed height calibration is used.
