module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeDifferenceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSuccessorIntroductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchMemoThinLookupChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowThinTableProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename headTransport)
open ID1Completion.InternalEqualityTest (subtract)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalListCodec (consCode headCode)
open ID1Completion.InternalListCodecSupportProof (consGraph consDestruction)
open ID1Completion.InternalRawListRecursion (lookup)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalRecursionGraphSuccessorIntroductionProof (recursionSuccessorIntroduction)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalScratchMemoThinLookupChecks (tableLookup)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalAuxWindowOpenTargets
open NumberedWindowInternalAuxMeasureStepTargets (childAt offsetAt measureAt)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (binaryGraph)
open NumberedWindowInternalSparseDecodeDifferenceProof (differenceEquation)
open NumberedWindowInternalSparseFieldParser (scratchTable scratchRow scratchBase scratchStep)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename quadInputsRename)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private def inputs : Fin 3 → Program 2 :=
  Fin.cons (.projection 1) (Fin.cons (.projection 0) (Fin.cons (constantZero 2) Fin.elim0))

private theorem selectedParams (ctx raw : OTerm α) : ∀ i : Fin 3,
    Nonempty (Derivation body Γ (programGraph (inputs i) ((![raw,ctx,z] : Fin 3 → OTerm α) i) ![ctx,raw])) := by
  intro i
  exact Fin.cases (projectionValue 1 ![ctx,raw])
    (Fin.cases (projectionValue 0 ![ctx,raw]) (Fin.cases (zeroConstantValue ![ctx,raw]) (fun j => Fin.elim0 j))) i

theorem sameContext (R : Program 4) (out ctx raw : OTerm α) :
    Nonempty (Derivation body Γ (intrinsicGraph (selectedIntrinsic R) out ctx raw)) ↔
    Nonempty (Derivation body Γ (contextRow R out raw ctx)) := by
  constructor
  · intro h
    exact compositionRecover (scratchRow (constantZero 2) R) inputs out ![ctx,raw] ![raw,ctx,z]
      h (selectedParams ctx raw)
  · intro h
    exact compositionValue (scratchRow (constantZero 2) R) inputs out ![ctx,raw] ![raw,ctx,z]
      h (selectedParams ctx raw)

private theorem tableAdvance (R : Program 4) (out key old ctx next : OTerm α)
    (tab : Nonempty (Derivation body Γ (contextTable R old key ctx)))
    (row : Nonempty (Derivation body Γ (contextStep R out key old ctx)))
    (cons : Nonempty (Derivation body Γ (consGraph next out old))) :
    Nonempty (Derivation body Γ (contextTable R next (suc key) ctx)) := by
  let xs : Fin 4 → OTerm α := ![key,old,ctx,z]
  have step : Nonempty (Derivation body Γ (programGraph (scratchStep R) next xs)) := by
    apply compositionValue consCode ![R,.projection 1] next xs ![out,old] cons
    intro i
    exact Fin.cases row (Fin.cases (projectionValue 1 xs) (fun j => Fin.elim0 j)) i
  exact recursionSuccessorIntroduction Γ (OrdinaryArithmetic.graphFormula (scratchBase (constantZero 2)))
    (OrdinaryArithmetic.graphFormula (scratchStep R)) next key old ![ctx,z] tab step

private theorem readHead (R : Program 4) (out key ctx table : OTerm α)
    (tab : Nonempty (Derivation body Γ (contextTable R table key ctx)))
    (head : Nonempty (Derivation body Γ (programGraph headCode out ![table]))) :
    Nonempty (Derivation body Γ (contextRow R out key ctx)) := by
  apply compositionValue headCode (fun _ : Fin 1 => scratchTable (constantZero 2) R)
    out ![key,ctx,z] ![table] head
  intro i
  obtain rfl := Fin.eq_zero i
  exact tab

theorem exact_OpenContextMemoSuccessor : ExactOpenContextMemoSuccessor := by
  intro R body α Γ out key old ctx tab row
  apply programCases consCode ![out,old] _
  intro β j Δ next hJ cons
  simp only [contextRow,programRename,tripleInputsRename,sucRelabel,zRelabel]
  simp only [binaryInputsRename] at cons
  have tab' := renameInto tab j Δ hJ
  have row' := renameInto row j Δ hJ
  simp only [contextTable,programRename,tripleInputsRename,zRelabel] at tab'
  simp only [contextStep,programRename,quadInputsRename,zRelabel] at row'
  obtain ⟨unpacked⟩ := consDestruction next (out.relabel j) (old.relabel j) cons
  exact readHead R (out.relabel j) (suc (key.relabel j)) (ctx.relabel j) next
    (tableAdvance R (out.relabel j) (key.relabel j) (old.relabel j) (ctx.relabel j) next tab' row' cons)
    ⟨Derivation.conjunctionLeft unpacked⟩

/-- Earlier lookup at the unchanged packed context, including arbitrary open terms. -/
theorem earlierValue (R : Program 4) (slot : Nat) (child value prior old ctx : OTerm α)
    (field : Nonempty (Derivation body Γ (programGraph (childAt slot) child ![prior,old,ctx,z])))
    (bound : Nonempty (Derivation body Γ (ltF child (suc prior))))
    (row : Nonempty (Derivation body Γ (contextRow R value child ctx)))
    (tab : Nonempty (Derivation body Γ (contextTable R old prior ctx))) :
    Nonempty (Derivation body Γ (programGraph (measureAt slot) value ![prior,old,ctx,z])) := by
  apply programCases subtract ![child,prior] _
  intro β j Δ off hJ sub
  simp only [programRename,quadInputsRename,zRelabel]
  simp only [binaryInputsRename] at sub
  have field' := renameInto field j Δ hJ
  have bound' := renameInto bound j Δ hJ
  have row' := renameInto row j Δ hJ
  have tab' := renameInto tab j Δ hJ
  simp only [programRename,quadInputsRename,zRelabel] at field'
  simp only [orderRename,sucRelabel] at bound'
  simp only [contextRow,programRename,tripleInputsRename,zRelabel] at row'
  simp only [contextTable,programRename,tripleInputsRename,zRelabel] at tab'
  let c := child.relabel j
  let k := prior.relabel j
  let old' := old.relabel j
  let ctx' := ctx.relabel j
  let xs : Fin 4 → OTerm β := ![k,old',ctx',z]
  obtain ⟨sum⟩ := differenceEquation c k off bound' sub
  have moved := headTransport (scratchTable (constantZero 2) R) old' k
    (OrdinaryArithmetic.addTerm c off) ![ctx',z] ⟨symm sum⟩ tab'
  have hit := tableLookup (constantZero 2) R (value.relabel j) c off old' ![ctx',z] row' moved
  have offset : Nonempty (Derivation body Δ (programGraph (offsetAt slot) off xs)) :=
    binaryGraph subtract (childAt slot) (.projection 0) off c k xs sub field' (projectionValue 0 xs)
  exact binaryGraph lookup (offsetAt slot) (.projection 1) (value.relabel j) off old' xs
    hit offset (projectionValue 1 xs)

#print axioms exact_OpenContextMemoSuccessor
#print axioms earlierValue

end LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowThinTableProof
