# Paper 17: thin prepared-parameter projection

**Target-only.** No new proof, native evidence, or numbered credit.

Printed source: arithmetic.tex, the already-normalized all-large
projection step (“Residues, finite strips, and one-variable projection”).
See the two Nov21 source reviews for the checked kernel and the table
lowering convention. Here all signed rows and Boolean placements,
including original domain/graph constraints, are inputs already prepared
by work outside this contract.

1. **Actual output program.** A raw packet is (exact table bytes,
   formula code). Run literal `LinearRows.Code.eliminate 0` and preserve
   the first component byte-for-byte for every raw packet. Effective
   `Primrec` and literal calibration to the actual
   `LinearRows.eliminate 0` formula on every typed formula are separate
   required clauses. The immutable table code retains tags, original
   lower rank, and actual ordinary/count syntax bytes. No reencoding or
   declaration of new lower field expressions in output.
2. **Grammar and support.** Prepared input has only literal variable
   summands, even at zero coefficient, and every positive name denotes
   an original table slot. The output must still have only plain
   variable summands, no zero name, and no additional names or names
   outside the same table. Exact support theorem pays only variable names;
   plain syntax must be preserved by the actual row, normalization,
   cutoff and instantiation operations separately.
3. **Arbitrary assignments first.** For every `ν : Nat → Nat`, not
   just realizable slot assignments, actual output formula evaluation at
   ν is iff existence of one natural z in the unchanged input formula
   with name zero updated. Uses the checked `actual_linear_elimination`
   supplier, not a lightweight new algorithm.
4. **One actual tied assignment.** Typed lower slots are raw coordinate,
   ordinary field, or count; each is read at its original rank under
   one shared valuation ρ. Read hits calibrate to the actual 724
   affine-input-free value/count relation with true domain and
   definedness, not fabricated numeric defaults. A tied table explicitly
   requires all ranks strictly below z's rank and values of every slot
   genuinely defined. Changing the eliminated raw rank and name zero
   by the same natural value leaves all tied lower reads untouched.
   The tied corollary has no independent existential quantification
   of the parameter entries; only z varies. Repeated ranks/fields are
   allowed but cannot be assigned independently of the actual reads.

**Not covered:** extraction or normalization of original nonlinear rows,
parity/modular table preparation, exact charge/cancellation bridge,
circuit flattening, identity cases beyond existing source supplies,
finite-strip substitution, successive dimensions, arbitrary alternation,
or either printed arithmetic theorem.
