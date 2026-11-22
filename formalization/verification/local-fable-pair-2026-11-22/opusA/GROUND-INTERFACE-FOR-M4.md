# Interface Opus A needs from M4 (`GroundScalarCircuit`), for M5 of `thm:ground`

Opus A, 2026-11-22. The `thm:ground` comparator is frozen:
`LogicLineages/PermittedControl/GroundComparisonTargets.lean`
(sha256 `1c4d40201de55c3f03f145914bb44ccd75de641fc2b59038c09de9931b6e2d91`).
Background is in `opusA/P17-GROUND-GAP.md` (item M4).

## What M5 does with it

From #261 (`SelectedGeneratedSourceTargets.TypedImage`), each term has a `CompiledVector` `c`, and the raw
compiler outputs `c.syntaxCode index = (scalarSyntaxCode index c.scalar, positive codes)`. Here
`index = fun x => SourceTypedPorts.variableIndex x.2.1`. M5 normalises the first component with the accepted
`normalizeScalarSyntaxCode`, which gives `scalarCode index c.scalar` by the accepted
`scalarSyntaxNormalizationCorrect`. It then needs **one closed existential query per counterexample relation**,
which it hands to `StageCallbackGuardRender.closedBlockDecision`.

## The statement I need (Lean, over existing declarations)

All names are existing declarations:
- `Scalar`, `scalarCode`: `OrdinalComparison.Source.ForwardTranslation`.
- `scalarValueWith`: `PermittedControl.SelectedGeneratedSource`.
- `Gate`, `Topological`: `PermittedControl.OriginalPrintedCircuitSequential`.
- `PlainPreparedFormula`: `PreparedProjection`.
- `Args`, `encodeInput`: `PermittedControl.OriginalPrintedRawFamilyFrontend`.
- `HasSuccessfulObservation`: `PermittedControl.OriginalPrintedTypedExistential`.
- `NormalForm.Formula`: `OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalForm`.

```lean
namespace LogicLineages.PermittedControl.GroundScalarCircuit

/-- Counterexample relation tags: 0 is `y < x` (E_A > E_B), 1 is `y ≤ x` (E_A ≥ E_B), and any
other tag is `x ≠ y`. -/
def Counter (tag : Nat) (x y : Nat) : Prop :=
  if tag = 0 then y < x else if tag = 1 then y ≤ x else x ≠ y

/-- Raw compiler: the relation tag and the two NORMALISED scalar codes (`scalarCode` form, heads
already `rawNoteEncode (scalarHeadNote c).1`) go to the closed-block query arguments. -/
def queryCode (tag a b : Nat) : OriginalPrintedRawFamilyFrontend.Args := …

def ExactQueryCode : Prop :=
  ∀ (tag : Nat) {ι : Type} (index : ι → Nat) (sa sb : Scalar ι),
    ∃ (known : List Nat) (gs : List OriginalPrintedCircuitSequential.Gate) (p : NormalForm.Formula),
      OriginalPrintedCircuitSequential.Topological known gs ∧ PreparedProjection.PlainPreparedFormula p ∧
      queryCode tag (scalarCode index sa) (scalarCode index sb) =
        OriginalPrintedRawFamilyFrontend.encodeInput known gs p true ∧
      ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
        (OriginalPrintedTypedExistential.HasSuccessfulObservation f gs p true ↔
          ∃ ν : Nat → Nat, (∀ n, 0 < ν n) ∧
            Counter tag (SelectedGeneratedSource.scalarValueWith f (fun x => ν (index x)) sa)
                        (SelectedGeneratedSource.scalarValueWith f (fun x => ν (index x)) sb))

def QueryCodeEffectivity : Prop := Primrec (fun x : Nat × Nat × Nat => queryCode x.1 x.2.1 x.2.2)
```

Notes:
- The **inputs are positive**: `ν n > 0` on every name. The circuit's raw inputs range over ℕ, so a variable leaf
  named `index x` should read `input + 1` through an affine gate, or equivalent.
- **Repeated `index` values must share one input**. Several variables with the same index are one coordinate.
- If you prefer `Computable` to `Primrec` in `QueryCodeEffectivity`, that works for me; please freeze one of the two.
- If quantifying `known/gs/p` outside `f` is awkward, it is fine to put `∀ f B, Selected… →` first. M5 only uses
  the equation and the iff together.
- If your frozen statement differs in form (argument order, uncurrying, tag encoding, a typed rather than a code
  compiler, or one compiler per relation), I will adapt in M5. Please only tell me if the semantics differ:
  something other than positive shared inputs, or a different relation.
