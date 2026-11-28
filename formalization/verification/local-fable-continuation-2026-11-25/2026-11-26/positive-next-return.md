The child program can be selected only as an opaque existential, but its top node can be made explicit. That one choice gives a successor-shaped object graph for symbolic inputs and a fully determined graph at literal body codes. What is still missing for a symbolic body is a term for the shifted code, which no existing derivation supplies. Nothing here is compiled or written.

## Trace

- **Source:** `NumberedWindowShiftProgramProof.outputPrim` is already cutoff-general (`output p.1 p.2.1 p.2.2`). `exact_LiteralShiftHit` throws the cutoff away by composing with `Primrec.const 0`.
- **Compiler:** `GorbowPRProgram.Proof.allPrimitiveFunctions` is `programOfTextbook (Nat.Primrec'.of_prim h)`. `programOfTextbook` is a private theorem by induction on a `Prop`, with `classical` and `choose` in the composition case. It yields `∃ p, ∀ v, evaluate p v = f v` and no AST.
- **Consequence:** a program can be picked with its numeric fit, but the only object-level facts about it are the generic ones:
  - `exact_NumeralGraph` at closed numerals;
  - `programCases` (totality) on open terms;
  - `valueUnique`.

  No derivation exists for a specific output term on symbolic input.
- **What I can make explicit:** the final successor. Take `T` for the bare code `((output m c n).1).getD 0` and use `.composition .succ (fun _ => T)`. Its output is then successor-shaped by construction, which is exactly the form the lambda row's `child` premise needs.

## Module

The two modules I gave in the last two turns (`…ShiftCut…` and `…ShiftLambdaRowNumericProof`) are not in the tree I can read, so this module does not depend on them. It uses pointwise evaluation equations rather than a named contract.

`LogicLineages/PersistentMarking/NumberedWindowInternalLiteralSingletonShiftCutChildProof.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaOpenRowsProof
import LogicLineages.PersistentMarking.NumberedWindowShiftProgramProof
import LogicLineages.PersistentMarking.NumberedWindowNumeralGraphChecks
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftCutChildProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue successorValue)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalEqualityTestEvaluationProof (vectorOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program evaluate)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowNumeralGraphChecks (exact_NumeralGraph)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (shiftHitValue)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambdaDispatch)
open NumberedWindowInternalLiteralSingletonLambdaOpenRowsProof (exact_OpenSingletonLambdaDispatch)
open NumberedWindowShiftAlgorithm (output)

/-- The cutoff-general code program, from the same `outputPrim` that
supplies the installed shift hit, with the cutoff kept as an input. -/
theorem exact_ShiftCutCodeProgram :
    ∃ T : Program 3, ∀ m c n,
      evaluate T (List.Vector.cons m (List.Vector.cons c (List.Vector.cons n List.Vector.nil))) =
        ((output m c n).1).getD 0 := by
  let X := List.Vector Nat 3
  have amount : Primrec (fun v : X => v.head) := Primrec.vector_head
  have tail : Primrec (fun v : X => v.tail) := Primrec.vector_tail
  have cutoff : Primrec (fun v : X => v.tail.head) := Primrec.vector_head.comp tail
  have code : Primrec (fun v : X => v.tail.tail.head) :=
    Primrec.vector_head.comp (Primrec.vector_tail.comp tail)
  have full := NumberedWindowShiftProgramProof.outputPrim.comp (amount.pair (cutoff.pair code))
  have first := Primrec.fst.comp full
  have packed := Primrec.option_getD.comp first (Primrec.const 0)
  obtain ⟨p,ok⟩ :=
    LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Proof.allPrimitiveFunctions 3 _ packed
  exact ⟨p,fun m c n => ok _⟩

/-- With the successor written explicitly, the value is the original
shift value at every amount, cutoff and code. -/
theorem exact_ShiftCutSuccFit (T : Program 3)
    (fit : ∀ m c n,
      evaluate T (List.Vector.cons m (List.Vector.cons c (List.Vector.cons n List.Vector.nil))) =
        ((output m c n).1).getD 0) (m c n : Nat) :
    evaluate (.composition .succ (fun _ : Fin 1 => T) : Program 3)
      (List.Vector.cons m (List.Vector.cons c (List.Vector.cons n List.Vector.nil))) =
        ((output m c n).1).getD 0 + 1 := by
  rw [evaluate,vectorOne]
  change evaluate T
    (List.Vector.cons m (List.Vector.cons c (List.Vector.cons n List.Vector.nil))) + 1 = _
  rw [fit m c n]

/-- Its cutoff-zero slice is the installed shift-hit value. -/
theorem exact_ShiftCutSuccAtZero (T : Program 3)
    (fit : ∀ m c n,
      evaluate T (List.Vector.cons m (List.Vector.cons c (List.Vector.cons n List.Vector.nil))) =
        ((output m c n).1).getD 0) (a d : Nat) :
    evaluate (.composition .succ (fun _ : Fin 1 => T) : Program 3)
      (List.Vector.cons d (List.Vector.cons 0 (List.Vector.cons a List.Vector.nil))) =
        shiftHitValue a d :=
  exact_ShiftCutSuccFit T fit d 0 a

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Child graph at literal amount, cutoff and body code: the output is
the successor of the numeral of the actual shift output at the
incremented cutoff. One evaluation equation is the only numeric input. -/
theorem exact_OpenShiftCutChildNumeral (T : Program 3) (m c b : Nat)
    (value : evaluate T
      (List.Vector.cons m (List.Vector.cons (c+1) (List.Vector.cons b List.Vector.nil))) =
        ((output m (c+1) b).1).getD 0) :
    D B Γ (programGraph (.composition .succ (fun _ : Fin 1 => T) : Program 3)
      (suc (numeral (((output m (c+1) b).1).getD 0)))
      ![numeral m,suc (numeral c),numeral b]) := by
  have literal := exact_NumeralGraph 3 T
    (List.Vector.cons m (List.Vector.cons (c+1) (List.Vector.cons b List.Vector.nil))) B α Γ
  have tape : NumberedWindowNumeralGraphTargets.inputs
      (List.Vector.cons m (List.Vector.cons (c+1) (List.Vector.cons b List.Vector.nil))) =
      (![numeral m,suc (numeral c),numeral b] : Fin 3 → OTerm α) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · obtain rfl := Fin.eq_zero k
        rfl
  rw [tape,value] at literal
  apply compositionValue .succ (fun _ : Fin 1 => T)
    (suc (numeral (((output m (c+1) b).1).getD 0))) _
    ![numeral (((output m (c+1) b).1).getD 0)]
    (successorValue ![numeral (((output m (c+1) b).1).getD 0)])
  intro i
  obtain rfl := Fin.eq_zero i
  exact literal

/-- Child graph at symbolic amount, cutoff and body, in elimination
form. Totality of `T` gives some code `u` in an extended context; the
explicit successor makes the output `suc u`, so no zero branch arises. -/
theorem exact_OpenShiftCutChildCases (T : Program 3) (m c b : OTerm α) (ψ : Formula α)
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (u : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (programGraph (.composition .succ (fun _ : Fin 1 => T) : Program 3) (suc u)
        (fun i => ((![m,suc c,b] : Fin 3 → OTerm α) i).relabel j)) →
      D B Δ (ψ.relabel j)) :
    D B Γ ψ := by
  apply programCases T (![m,suc c,b] : Fin 3 → OTerm α) ψ
  intro β j Δ v keep hv
  apply k β j Δ v keep
  apply compositionValue .succ (fun _ : Fin 1 => T) (suc v) _ ![v] (successorValue ![v])
  intro i
  obtain rfl := Fin.eq_zero i
  exact hv

/-- Direct consumption by the existing lambda row: literal amount,
cutoff and body code, symbolic type field. -/
theorem exact_OpenShiftLambdaDispatchAtLiteralBody (T : Program 3) (m c b : Nat) (ty : OTerm α)
    (value : evaluate T
      (List.Vector.cons m (List.Vector.cons (c+1) (List.Vector.cons b List.Vector.nil))) =
        ((output m (c+1) b).1).getD 0) :
    D B Γ (programGraph
      (singletonLambdaDispatch (.composition .succ (fun _ : Fin 1 => T) : Program 3))
      (suc (rawLambdaTerm ty (numeral (((output m (c+1) b).1).getD 0))))
      ![numeral m,numeral c,rawLambdaTerm ty (numeral b)]) :=
  exact_OpenSingletonLambdaDispatch (.composition .succ (fun _ : Fin 1 => T) : Program 3)
    (numeral m) (numeral c) ty (numeral b) (numeral (((output m (c+1) b).1).getD 0))
    (exact_OpenShiftCutChildNumeral T m c b value)

#print axioms exact_ShiftCutCodeProgram
#print axioms exact_ShiftCutSuccFit
#print axioms exact_ShiftCutSuccAtZero
#print axioms exact_OpenShiftCutChildNumeral
#print axioms exact_OpenShiftCutChildCases
#print axioms exact_OpenShiftLambdaDispatchAtLiteralBody
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftCutChildProof
```

## Who consumes what

| Supplied here | Existing consumer | Premise it fills |
|---|---|---|
| `exact_OpenShiftCutChildNumeral` | `exact_OpenSingletonLambdaDispatch` (`LambdaOpenRowsProof`) | `child : programGraph U (suc b') ![a, suc d, b]` |
| `exact_ShiftCutSuccFit` at `(m, c+1, b)` | `exact_LiteralLambdaDispatchValue` with the saved `exact_ShiftLambdaRowValue` | the child evaluation equation of the numeric lambda row |
| `exact_ShiftCutSuccAtZero` | any theorem asking for `ShiftHitFit H` once the program is re-taped as `[d, 0, a]` | value agreement with `shiftHitValue` |

The table parameter is tied in by the saved bridge: for a valid lambda node `n` with body `b`, `((output m (c+1) b).1).getD 0` is `(earlier (table m c n n) b 1).1`.

## What is still missing

- **Symbolic body, definite output.** For an open term `b` there is no object-language term for the shifted code. `exact_OpenShiftCutChildCases` gives the most that is derivable: some `u`, in an extended context, with the child output `suc u`. A consumer has to work under the renaming `j` (the saved `dispatchBottom` in `AtomsOpenProof` shows the pattern with `tripleInputsRename`) and conclude an existential or eliminative statement. I have not written that consumer.
- **Why this cannot be closed further.** The equation relating `u` to anything else would need an open derivation about `T`'s graph: for instance, that the table entry it returns satisfies the tag-2 row equation on open codes. `T` is opaque below its top node, so that needs a certificate-carrying program for `table`/`earlier`. That is the same course-of-values dependency as before, now isolated to `T`.
- **Re-taping to `H`.** `exact_ShiftCutSuccAtZero` gives the value on `[d, 0, a]`; the two-slot re-taped program itself is not on disk.

**Unverified points:**
- `ok _` in `exact_ShiftCutCodeProgram` must unify the vector from the left-hand side and match the `Primrec` lambda by unfolding, as `exact_LiteralShiftHit` does with an explicit vector.
- `rw [evaluate,vectorOne]` in `exact_ShiftCutSuccFit` mirrors the `retainSingleton` precedent.
- In `exact_OpenShiftCutChildCases`, the `(xs i).relabel j` form must match what `programCases` produces.
