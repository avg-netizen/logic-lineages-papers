module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitMachineProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenHitProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowNumeralGraphChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitOpenProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.InternalArithmeticPrograms (addition)
open ID1Completion.InternalArithmeticProgramsSupportProof (additionValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program evaluate)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (consOfGraph)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowNumeralGraphChecks (exact_NumeralGraph)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralSingletonAtomsNumericProof (singletonSyntax)
open NumberedWindowInternalLiteralSingletonAtomsOpenProof (exact_OpenSingletonSyntax)
open NumberedWindowInternalLiteralSingletonBoundMachineProof
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof
open NumberedWindowInternalLiteralSingletonBoundOpenHitProof (exact_OpenSingletonBoundAtPositiveDepth)
open NumberedWindowInternalLiteralSingletonShiftHitMachineProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The raised-index emitter on an open packed bound node in tape slot 2.
Type field, index and depth are arbitrary terms; the sum is the actual
addition program's open graph. The first slot is never read. -/
theorem exact_OpenShiftBoundRaised (a d ty i : OTerm α) :
    D B Γ (programGraph shiftBoundRaised (suc (boundTerm ty (add i d)))
      ![a,d,boundTerm ty i]) := by
  let q := boundTerm ty i
  let xs : Fin 3 → OTerm α := ![a,d,q]
  have rows := exact_OpenBoundRead (B := B) (Γ := Γ) ty i
  have tyGraph : D B Γ (programGraph boundType ty xs) := onTape (field 0) 2 ty xs rows.2.1
  have idxGraph : D B Γ (programGraph boundIndex i xs) := onTape (field 1) 2 i xs rows.2.2
  have raised : D B Γ (programGraph shiftRaisedIndex (add i d) xs) := by
    apply compositionValue addition (![boundIndex,.projection 1] : Fin 2 → Program 3)
      (add i d) xs ![i,d] (additionValue i d)
    intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact idxGraph
    · obtain rfl := Fin.eq_zero j
      exact projectionValue (1 : Fin 3) xs
  have tailGraph := consOfGraph shiftRaisedIndex (constantZero 3) (add i d) z xs raised
    (constantZeroValue xs)
  have bodyGraph := consOfGraph boundType (consOf shiftRaisedIndex (constantZero 3))
    ty (rawCons (add i d) z) xs tyGraph tailGraph
  have code : D B Γ (programGraph shiftBoundCode (boundTerm ty (add i d)) xs) :=
    consOfGraph (literal 3 1) (consOf boundType (consOf shiftRaisedIndex (constantZero 3)))
      (numeral 1) (rawCons ty (rawCons (add i d) z)) xs (literalGraph 1 xs) bodyGraph
  apply compositionValue .succ (fun _ : Fin 1 => shiftBoundCode)
    (suc (boundTerm ty (add i d))) xs ![boundTerm ty (add i d)]
    (successorValue ![boundTerm ty (add i d)])
  intro k
  obtain rfl := Fin.eq_zero k
  exact code

/-- Open graph of the physical shift-hit program on a typed bound literal
replacement. The only premise is the retained syntax/typing guard on the
replacement; nothing is assumed about the fallback `H`. -/
theorem exact_OpenShiftHitBound (V : Program 1) (H : Program 2) (ty i d : OTerm α)
    (typed : D B Γ (unary V (suc z) (boundTerm ty i))) :
    D B Γ (programGraph (shiftHitBound V H) (suc (boundTerm ty (add i d)))
      ![boundTerm ty i,d]) := by
  let q := boundTerm ty i
  let out := suc (boundTerm ty (add i d))
  let xs : Fin 3 → OTerm α := ![q,d,q]
  have valid : D B Γ (bit (singletonSyntax V) xs) := exact_OpenSingletonSyntax V q d q typed typed
  have isBound : D B Γ (bit (onRaw boundShape 2) xs) :=
    onTape boundShape 2 (suc z) xs (exact_OpenBoundRead ty i).1
  have raised : D B Γ (programGraph shiftBoundRaised out xs) :=
    exact_OpenShiftBoundRaised q d ty i
  have inner : D B Γ (programGraph
      (branch (onRaw boundShape 2) (shiftHitFallback H) shiftBoundRaised) out xs) :=
    successorBranchIntro (onRaw boundShape 2) (shiftHitFallback H) shiftBoundRaised
      out z xs isBound raised
  have dispatched : D B Γ (programGraph (shiftHitDispatch V H) out xs) :=
    successorBranchIntro (singletonSyntax V) (shiftHitFallback H)
      (branch (onRaw boundShape 2) (shiftHitFallback H) shiftBoundRaised) out z xs valid inner
  apply compositionValue (shiftHitDispatch V H)
    (![.projection 0,.projection 1,.projection 0] : Fin 3 → Program 2) out ![q,d] xs dispatched
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · exact projectionValue (0 : Fin 2) ![q,d]
  · refine Fin.cases ?_ (fun l => ?_) j
    · exact projectionValue (1 : Fin 2) ![q,d]
    · obtain rfl := Fin.eq_zero l
      exact projectionValue (0 : Fin 2) ![q,d]

/-- The positive-depth equal-index row with its `H` premise discharged for
a bound literal replacement: all four fields and the depth are symbolic,
and both syntax premises are retained. -/
theorem exact_OpenSingletonBoundShiftedBoundLiteral (V : Program 1) (H : Program 2)
    (U : Program 3) (ty i d t : OTerm α)
    (inserted : D B Γ (unary V (suc z) (boundTerm ty i)))
    (typedNode : D B Γ (unary V (suc z) (boundTerm t (suc d)))) :
    D B Γ (programGraph (singletonBound V (shiftHitBound V H) U)
      (suc (boundTerm ty (add i (suc d))))
      ![boundTerm ty i,suc d,boundTerm t (suc d)]) :=
  exact_OpenSingletonBoundAtPositiveDepth V (shiftHitBound V H) U (boundTerm ty i) d t
    (suc (boundTerm ty (add i (suc d)))) inserted typedNode
    (exact_OpenShiftHitBound V H ty i (suc d) inserted)

/-- Any program at a numeral replacement code and a positive numeral
depth: the literal graph at its actual value. This is what is available
for the existential fallback itself. -/
theorem exact_OpenShiftHitNumeral (H : Program 2) (n k : Nat) :
    D B Γ (programGraph H
      (numeral (evaluate H (List.Vector.cons n (List.Vector.cons (k+1) List.Vector.nil))))
      ![numeral n,suc (numeral k)]) := by
  have literal := exact_NumeralGraph 2 H
    (List.Vector.cons n (List.Vector.cons (k+1) List.Vector.nil)) B α Γ
  have tape : NumberedWindowNumeralGraphTargets.inputs
      (List.Vector.cons n (List.Vector.cons (k+1) List.Vector.nil)) =
      (![numeral n,suc (numeral k)] : Fin 2 → OTerm α) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · obtain rfl := Fin.eq_zero j
      rfl
  rw [tape] at literal
  exact literal

/-- Numeral-level positive hit for an arbitrary `H`; the node's type field
stays symbolic. -/
theorem exact_OpenSingletonBoundAtPositiveNumeral (V : Program 1) (H : Program 2)
    (U : Program 3) (n k : Nat) (t : OTerm α)
    (inserted : D B Γ (unary V (suc z) (numeral n)))
    (typedNode : D B Γ (unary V (suc z) (boundTerm t (suc (numeral k))))) :
    D B Γ (programGraph (singletonBound V H U)
      (numeral (evaluate H (List.Vector.cons n (List.Vector.cons (k+1) List.Vector.nil))))
      ![numeral n,suc (numeral k),boundTerm t (suc (numeral k))]) :=
  exact_OpenSingletonBoundAtPositiveDepth V H U (numeral n) (numeral k) t
    (numeral (evaluate H (List.Vector.cons n (List.Vector.cons (k+1) List.Vector.nil))))
    inserted typedNode (exact_OpenShiftHitNumeral H n k)

#print axioms exact_OpenShiftBoundRaised
#print axioms exact_OpenShiftHitBound
#print axioms exact_OpenSingletonBoundShiftedBoundLiteral
#print axioms exact_OpenShiftHitNumeral
#print axioms exact_OpenSingletonBoundAtPositiveNumeral
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitOpenProof
