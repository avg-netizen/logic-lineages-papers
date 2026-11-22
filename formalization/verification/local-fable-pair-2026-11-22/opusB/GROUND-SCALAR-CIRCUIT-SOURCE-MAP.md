# GROUND-SCALAR-CIRCUIT — source map (Opus B), Task 7 = M4 of `thm:ground`

## Group A (typed compiler: shape + semantics)

Targets: `LogicLineages/PermittedControl/GroundScalarCircuitTargets.lean` (namespace
`LogicLineages.PermittedControl.GroundScalarCircuit`), sha256
`bcd325cc3566354e748cd7c6536e0bb7315b7ad155edc8ef63d3d275bb6917af`, frozen 22:51Z after compiling alone (receipt
`1795387859861003022-3163107`). It follows `opusA/GROUND-INTERFACE-FOR-M4.md`; `Counter` is copied verbatim.

### Compiler
- Raw input index `i` sits at the even name `2i`.
- Circuit node `k` sits at the odd name `2k+1`.
- `circuitOf index s k` returns (gates, output, next counter):
  - `one` → affine gate `1`;
  - `var x` → affine gate `1 + input(index x)`, i.e. the positive value. Repeated indices read the same input name.
  - `add` → the two subcircuits, then an affine sum;
  - `shift c a` → the subcircuit, then one collapse wire with head `scalarHeadNote c`.
- `block index tag A B`:
  - known = every input name below `scalarCode A + scalarCode B + 1`;
  - gates = left circuit from counter 0, then right circuit continuing the counter;
  - matrix = `counterFormula tag` on the two output nodes: `strictRow`/`weakRow`, or a disjunction of two strict rows for `≠`.

### Statements
- `BlockShape`: `Topological known gates ∧ PlainPreparedFormula matrix`.
- `BlockCorrect`: at every `SelectedWithThreshold f K`,
  `HasSuccessfulObservation f gates matrix true ↔ ∃ ν, (∀ n, 0 < ν n) ∧ Counter tag (scalarValueWith f (fun x => ν (index x)) A) (… B)`.

### Conversions
- Raw circuit inputs range over ℕ; scalar inputs are positive. The affine `+1` in the `var` gate converts between them, and
  the proof does the conversion (`ν n = base(2n)+1`), not a hypothesis.
- Sharing: the valuation is one function of the index.

### Assumed / not claimed
Nothing beyond accepted gate semantics:
- `ArbitraryFixedHeadCollapse.ActualGraph`;
- `rawNoteDecodeEncode`;
- the `scalarHeadNote` repr lemma, which is re-proved.
