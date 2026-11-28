The tag-2 row cannot be hosted by `H` itself: `H(a,d)` is the shift at cutoff 0, and a lambda body is shifted at cutoff 1. One existing provider does suffice for the open side once the cutoff is a tape slot. The numeric side is still missing, and I state it as an exact target instead of proving it. Nothing is compiled or written.

## Trace of the tag-2 row

- **Algorithm:** `NumberedWindowShiftAlgorithm.termParts`, tag 2, returns `packNode 2 [atField 0, (earlier t (atField 1) (offset+1)).1]`. The body is read from the table one offset up.
- **Table certificate (numeric only):** `NumberedWindowShiftTableProof.earlierExact` and `computedNode`, used by the `.lam` case of `NumberedWindowShiftProof.term`, packaged as `matrix` / `NumberedWindowShiftChecks.exact_ShiftMatrix` and `exact_ShiftOutput`.
- **Program:** in `NumberedWindowShiftStepPrograms.termPartsPrim` the read is the local `body`, built from `earlierPrim` at `Primrec.succ.comp offset`. It then flows through `termNextPrim`, `NumberedWindowShiftProgramProof.outputPrim`, and `GorbowPRProgram.Proof.allPrimitiveFunctions` (`programOfTextbook`).
- **Installed `H`:** `exact_LiteralShiftHit` fixes cutoff `0` and exposes no program term, so there is no graph of `earlier`, `table` or the lambda row.

**Closest installed obligations:**
- `ShiftHitFit H` is the only contract on `H`. It is consumed at `exact_LiteralShiftedInsertion`, only when `d ≠ 0` and with `(syntaxBits a).1 = true` in scope.
- The singleton lane's analogue for its own lambda row is `slotFit : GuardedDepthInstanceFit (singletonLambdaDispatch U)` in `exact_LiteralSingletonLambdaCalibrationOfGuarded`, still unproved.
- TARGETS.md checkpoint 4 names the raw-preservation premise. `exact_CheckedSingletonRawPreservation` covers it numerically under `DepthInstanceFit U`; I did not trace its open counterpart.

## What the existing provider gives

`singletonLambdaDispatch` and `exact_OpenSingletonLambdaDispatch` are generic in the slot program and in slot 0. They read slot 1 as a binder count and bump it by one. On the tape `[amount, cutoff, code]` that is exactly the shift lambda row. I add only:
- a re-taping `shiftCutAtZero` (no branch);
- one reuse of the original `V` guard on the code slot (`shiftCutLambda`).

The `V` guard is needed because an unguarded lambda dispatch would rebuild a node on an ill-typed lambda code, where the original value is `1`.

### Module 1: machine and target

`LogicLineages/PersistentMarking/NumberedWindowInternalLiteralSingletonShiftCutMachineProof.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitAtomsMachineProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaMachineProof
import LogicLineages.PersistentMarking.NumberedWindowShiftProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftCutMachineProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch constantZero)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalLiteralLambdaLexicalGateNumericProof (evalTernaryComposition)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (ShiftHitFit shiftHitValue)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambdaDispatch)
open NumberedWindowInternalLiteralSingletonShiftHitAtomsMachineProof
  (shiftHitLiterals exact_ShiftHitLiteralsFit)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax)
open NumberedWindowShiftAlgorithm (output)

/-- The shift value with its cutoff kept as an input. -/
def shiftCutValue (amount cutoff n : Nat) : Nat := ((output amount cutoff n).1).getD 0 + 1

/-- Contract of a shift program on the tape `[amount,cutoff,code]`. -/
def ShiftCutFit (S : Program 3) : Prop :=
  ∀ amount cutoff n, evaluate S (amount ::ᵥ cutoff ::ᵥ n ::ᵥ nil) = shiftCutValue amount cutoff n

theorem exact_LiteralShiftCut : ∃ S : Program 3, ShiftCutFit S := by
  let X := List.Vector Nat 3
  have amount : Primrec (fun v : X => v.head) := Primrec.vector_head
  have tail : Primrec (fun v : X => v.tail) := Primrec.vector_tail
  have cutoff : Primrec (fun v : X => v.tail.head) := Primrec.vector_head.comp tail
  have code : Primrec (fun v : X => v.tail.tail.head) :=
    Primrec.vector_head.comp (Primrec.vector_tail.comp tail)
  have full := NumberedWindowShiftProgramProof.outputPrim.comp (amount.pair (cutoff.pair code))
  have first := Primrec.fst.comp full
  have packed := Primrec.succ.comp (Primrec.option_getD.comp first (Primrec.const 0))
  obtain ⟨p,ok⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 3 _ packed
  exact ⟨p,fun m c n => ok (m ::ᵥ c ::ᵥ n ::ᵥ nil)⟩

/-- Read a cutoff-parameterized program as a shift-hit program: the tape
`[a,d]` becomes `[d,0,a]`. No branch is added. -/
def shiftCutAtZero (R : Program 3) : Program 2 :=
  .composition R ![.projection 1,constantZero 2,.projection 0]

/-- The lambda row behind the original syntax guard on the code slot.
The child call is the existing `lambdaChild`, at the bumped cutoff. -/
def shiftCutLambda (V : Program 1) (S : Program 3) : Program 3 :=
  branch (onRaw V 2) S (singletonLambdaDispatch S)

/-- A cutoff-parameterized fit gives the existing shift-hit contract. -/
theorem exact_ShiftCutAtZeroFit (R : Program 3) (fit : ShiftCutFit R) :
    ShiftHitFit (shiftCutAtZero R) := by
  intro a d
  rw [shiftCutAtZero,evalTernaryComposition]
  exact fit d 0 a

/-- The installed literal front over an opaque cutoff-parameterized shift
keeps the existing contract. -/
theorem exact_ShiftHitLiteralsCutFit (V : Program 1) (S : Program 3)
    (vFit : ActualRawSyntax V) (sFit : ShiftCutFit S) :
    ShiftHitFit (shiftHitLiterals V (shiftCutAtZero S)) :=
  exact_ShiftHitLiteralsFit V (shiftCutAtZero S) vFit (exact_ShiftCutAtZeroFit S sFit)

/-- The missing numeric obligation, stated exactly: the guarded lambda
row preserves the cutoff-parameterized contract. It is not proved here. -/
def ShiftCutLambdaRowFit (V : Program 1) : Prop :=
  ActualRawSyntax V → ∀ S : Program 3, ShiftCutFit S → ShiftCutFit (shiftCutLambda V S)

/-- Under that one obligation the lambda row is installable as the
actual `H` of the saved front, with the existing contract. -/
theorem exact_ShiftHitLiteralsOfLambdaRowFit (V : Program 1) (S : Program 3)
    (vFit : ActualRawSyntax V) (sFit : ShiftCutFit S) (row : ShiftCutLambdaRowFit V) :
    ShiftHitFit (shiftHitLiterals V (shiftCutAtZero (shiftCutLambda V S))) :=
  exact_ShiftHitLiteralsFit V (shiftCutAtZero (shiftCutLambda V S)) vFit
    (exact_ShiftCutAtZeroFit (shiftCutLambda V S) (row vFit S sFit))

#print axioms exact_LiteralShiftCut
#print axioms shiftCutLambda
#print axioms exact_ShiftCutAtZeroFit
#print axioms exact_ShiftHitLiteralsCutFit
#print axioms ShiftCutLambdaRowFit
#print axioms exact_ShiftHitLiteralsOfLambdaRowFit
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftCutMachineProof
```

### Module 2: open lambda row and transport

`LogicLineages/PersistentMarking/NumberedWindowInternalLiteralSingletonShiftCutOpenProof.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftCutMachineProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitAtomsOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaOpenRowsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftCutOpenProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (singletonBound)
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof (boundTerm)
open NumberedWindowInternalLiteralSingletonBoundOpenHitProof (exact_OpenSingletonBoundAtPositiveDepth)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambdaDispatch)
open NumberedWindowInternalLiteralSingletonLambdaOpenRowsProof (exact_OpenSingletonLambdaDispatch)
open NumberedWindowInternalLiteralSingletonShiftHitAtomsMachineProof (shiftHitLiterals)
open NumberedWindowInternalLiteralSingletonShiftHitAtomsOpenProof (exact_OpenShiftHitLiteralsOtherTag)
open NumberedWindowInternalLiteralSingletonShiftCutMachineProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The re-taping at cutoff zero: both projections and the literal zero
are derived on the tape `[a,d]`. -/
theorem exact_OpenShiftCutAtZero (R : Program 3) (a d out : OTerm α)
    (run : D B Γ (programGraph R out ![d,z,a])) :
    D B Γ (programGraph (shiftCutAtZero R) out ![a,d]) := by
  let xs : Fin 2 → OTerm α := ![a,d]
  apply compositionValue R ![.projection 1,constantZero 2,.projection 0] out xs ![d,z,a] run
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact projectionValue 1 xs
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact constantZeroValue xs
    · obtain rfl := Fin.eq_zero k
      exact projectionValue 0 xs

/-- The guarded lambda row at an arbitrary amount and cutoff. The only
premise about the body is an open graph of the slot program at the
bumped cutoff; the row itself is the existing lambda dispatch. -/
theorem exact_OpenShiftCutLambda (V : Program 1) (S : Program 3) (m c ty b b' : OTerm α)
    (typed : D B Γ (unary V (suc z) (rawLambdaTerm ty b)))
    (child : D B Γ (programGraph S (suc b') ![m,suc c,b])) :
    D B Γ (programGraph (shiftCutLambda V S) (suc (rawLambdaTerm ty b'))
      ![m,c,rawLambdaTerm ty b]) := by
  let xs : Fin 3 → OTerm α := ![m,c,rawLambdaTerm ty b]
  have accepted : D B Γ (programGraph (onRaw V 2) (suc z) xs) := onTape V 2 (suc z) xs typed
  exact successorBranchIntro (onRaw V 2) S (singletonLambdaDispatch S)
    (suc (rawLambdaTerm ty b')) z xs accepted
    (exact_OpenSingletonLambdaDispatch S m c ty b b' child)

/-- The shift-hit program built from that row, on a typed lambda
replacement: the child is the body at cutoff one. -/
theorem exact_OpenShiftCutLambdaHit (V : Program 1) (S : Program 3) (ty b b' d : OTerm α)
    (typed : D B Γ (unary V (suc z) (rawLambdaTerm ty b)))
    (child : D B Γ (programGraph S (suc b') ![d,suc z,b])) :
    D B Γ (programGraph (shiftCutAtZero (shiftCutLambda V S)) (suc (rawLambdaTerm ty b'))
      ![rawLambdaTerm ty b,d]) :=
  exact_OpenShiftCutAtZero (shiftCutLambda V S) (rawLambdaTerm ty b) d
    (suc (rawLambdaTerm ty b'))
    (exact_OpenShiftCutLambda V S d z ty b b' typed child)

/-- The saved front passes a typed lambda replacement to its `H`. -/
theorem exact_OpenShiftHitLiteralsLambda (V : Program 1) (H : Program 2)
    (ty b d out : OTerm α)
    (typed : D B Γ (unary V (suc z) (rawLambdaTerm ty b)))
    (computed : D B Γ (programGraph H out ![rawLambdaTerm ty b,d])) :
    D B Γ (programGraph (shiftHitLiterals V H) out ![rawLambdaTerm ty b,d]) :=
  exact_OpenShiftHitLiteralsOtherTag V H 2 [ty,b] d out (by decide) (by decide) (by decide)
    typed computed

/-- Actual output of the installed front on a typed lambda replacement,
under the child premise alone. -/
theorem exact_OpenShiftHitLiteralsLambdaRow (V : Program 1) (S : Program 3)
    (ty b b' d : OTerm α)
    (typed : D B Γ (unary V (suc z) (rawLambdaTerm ty b)))
    (child : D B Γ (programGraph S (suc b') ![d,suc z,b])) :
    D B Γ (programGraph (shiftHitLiterals V (shiftCutAtZero (shiftCutLambda V S)))
      (suc (rawLambdaTerm ty b')) ![rawLambdaTerm ty b,d]) :=
  exact_OpenShiftHitLiteralsLambda V (shiftCutAtZero (shiftCutLambda V S)) ty b d
    (suc (rawLambdaTerm ty b')) typed (exact_OpenShiftCutLambdaHit V S ty b b' d typed child)

/-- Positive-depth equal-index row for a lambda replacement. Both syntax
premises are retained; the child is the body shifted by the depth at
cutoff one. -/
theorem exact_OpenSingletonBoundShiftedLambdaLiteral (V : Program 1) (S : Program 3)
    (U : Program 3) (ty b b' d t : OTerm α)
    (inserted : D B Γ (unary V (suc z) (rawLambdaTerm ty b)))
    (typedNode : D B Γ (unary V (suc z) (boundTerm t (suc d))))
    (child : D B Γ (programGraph S (suc b') ![suc d,suc z,b])) :
    D B Γ (programGraph
      (singletonBound V (shiftHitLiterals V (shiftCutAtZero (shiftCutLambda V S))) U)
      (suc (rawLambdaTerm ty b')) ![rawLambdaTerm ty b,suc d,boundTerm t (suc d)]) :=
  exact_OpenSingletonBoundAtPositiveDepth V
    (shiftHitLiterals V (shiftCutAtZero (shiftCutLambda V S))) U (rawLambdaTerm ty b) d t
    (suc (rawLambdaTerm ty b')) inserted typedNode
    (exact_OpenShiftHitLiteralsLambdaRow V S ty b b' (suc d) inserted child)

#print axioms exact_OpenShiftCutAtZero
#print axioms exact_OpenShiftCutLambda
#print axioms exact_OpenShiftCutLambdaHit
#print axioms exact_OpenShiftHitLiteralsLambda
#print axioms exact_OpenShiftHitLiteralsLambdaRow
#print axioms exact_OpenSingletonBoundShiftedLambdaLiteral
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftCutOpenProof
```

## What is closed and what is not

**Closed at object level.** For a `V`-accepted symbolic lambda replacement, the installed front over `shiftCutAtZero (shiftCutLambda V S)` returns `suc (rawLambdaTerm ty b')` given only an open graph of `S` on `![d, suc z, b]`. It nests by taking `S := shiftCutLambda V S'`, as the singleton lane's lambda row does.

**Closed numerically.** `shiftCutAtZero S` satisfies the existing `ShiftHitFit` whenever `ShiftCutFit S`, and such an `S` exists. So moving `H` to the cutoff-parameterized interface costs nothing in the installation theorems.

**Missing, at the exact interface:**
- **`ShiftCutLambdaRowFit V`** (the numeric lambda row). My analysis says it is true, by this route:
  - for a valid lambda code, `exact_ShiftOutput` and the `.lam` clause of `shift` give `packNode 2 [ty, body'] + 1`;
  - the child value is nonzero and successor-packed;
  - on a `V`-rejected or non-lambda code the branch returns `S`.

  The proof needs the term codec on a lambda node and an evaluation lemma for `lambdaInstance`. I have not written it. It also assumes a valid lambda code has a valid body; I did not read `NumberedWindowSyntaxAlgorithm.termParts` to confirm.
- **The `child` premise** for a symbolic body of unbounded depth. That is the course-of-values dependency proper: an open graph for a program that reads `earlier (table …)`. Nothing in the tree supplies one; `earlierPrim` is the only handle.
- **Tags 4, 5, 6** read `argsNext` and the table's second component. They need their own rows and are not touched here.

**Fixes to saved modules.** None required. One correction to my earlier reports: I said the recursive tags "reach `H`" as if `H` could later host their rows. `H`'s tape has no cutoff slot, so the lambda row has to live in a three-slot program read through `shiftCutAtZero`, as above.

**Unverified points:**
- `exact fit d 0 a` in `exact_ShiftCutAtZeroFit` relies on `evaluate (constantZero 2) _` and the two projections reducing by unfolding.
- `exact_LiteralShiftCut` mirrors `exact_LiteralShiftHit` and `exact_LiteralDepthInstance`; the final `ok` must match `shiftCutValue` up to unfolding.
