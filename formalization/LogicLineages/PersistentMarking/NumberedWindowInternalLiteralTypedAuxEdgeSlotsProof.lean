module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (termReports)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (consOfGraph)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralTypedAuxEdgeGuardProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenEdgeSlotRead (p : Program 1) (i : Fin 4) (xs : Fin 4 → OTerm α) (v : OTerm α)
    (raw : D B Γ (unary p v (xs i))) : D B Γ (programGraph (readSlot p i) v xs) := by
  apply compositionValue p (Fin.cons (.projection i) Fin.elim0) v xs ![xs i] raw
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue i xs

theorem exact_OpenEdgeFieldMatch (xs : Fin 4 → OTerm α) (j : Nat) (a b : OTerm α)
    (l : D B Γ (unary (field j) a (xs 2))) (r : D B Γ (unary (field j) b (xs 3))) :
    (D B Γ (programGraph (sameField j) (suc z) xs) → D B Γ (eqn a b)) ∧
    (D B Γ (eqn a b) → D B Γ (programGraph (sameField j) (suc z) xs)) := by
  let P := fieldSlot 2 j
  let Q := fieldSlot 3 j
  let inputs : Fin 2 → Program 4 := Fin.cons P (Fin.cons Q Fin.elim0)
  let out : Fin 2 → OTerm α := Fin.cons a (Fin.cons b Fin.elim0)
  have pl := exact_OpenEdgeSlotRead (field j) 2 xs a l
  have pr := exact_OpenEdgeSlotRead (field j) 3 xs b r
  have args : ∀ i, D B Γ (programGraph (inputs i) (out i) xs) :=
    fun i => Fin.cases pl (Fin.cases pr (fun n => Fin.elim0 n)) i
  constructor
  · intro h
    unfold sameField at h
    rw [exact_DispatchControlAST.2.2.2.1] at h
    exact equalityOfAcceptance a b (compositionRecover equalityTest inputs (suc z) xs out h args)
  · intro eq
    unfold sameField
    rw [exact_DispatchControlAST.2.2.2.1]
    exact compositionValue equalityTest inputs (suc z) xs out (equalityOfEqual a b eq) args

structure AuxRow (α : Type) where
  dom : OTerm α
  cod : OTerm α
  fn : OTerm α
  arg : OTerm α

def AuxRow.term (row : AuxRow α) : OTerm α := auxiliaryTerm row.dom row.cod row.fn row.arg

def AuxRow.map {β : Type} (row : AuxRow α) (j : α → β) : AuxRow β :=
  ⟨row.dom.relabel j,row.cod.relabel j,row.fn.relabel j,row.arg.relabel j⟩

theorem exact_OpenFunctionChildEdge (E : Program 4) (ctx ty : OTerm α) (a b : AuxRow α) :
    let xs : Fin 4 → OTerm α := ![ctx,ty,a.term,b.term]
    (D B Γ (programGraph (functionChildEdge E) (suc z) xs) →
      D B Γ (acceptEdge E ctx (rawCons a.dom a.cod) a.fn b.fn)) ∧
    (D B Γ (acceptEdge E ctx (rawCons a.dom a.cod) a.fn b.fn) →
      D B Γ (programGraph (functionChildEdge E) (suc z) xs)) := by
  intro xs
  obtain ⟨_,fa⟩ := termReports (body := B) (Γ := Γ) a.dom a.cod a.fn a.arg
  obtain ⟨_,fb⟩ := termReports (body := B) (Γ := Γ) b.dom b.cod b.fn b.arg
  have ad := exact_OpenEdgeSlotRead (field 0) 2 xs a.dom fa.1
  have ac := exact_OpenEdgeSlotRead (field 1) 2 xs a.cod fa.2.1
  have af := exact_OpenEdgeSlotRead (field 2) 2 xs a.fn fa.2.2.1
  have bf := exact_OpenEdgeSlotRead (field 2) 3 xs b.fn fb.2.2.1
  have label : D B Γ (programGraph functionType (rawCons a.dom a.cod) xs) :=
    consOfGraph (fieldSlot 2 0) (fieldSlot 2 1) a.dom a.cod xs ad ac
  let input : Fin 4 → Program 4 := ![.projection 0,functionType,fieldSlot 2 2,fieldSlot 3 2]
  let results : Fin 4 → OTerm α := ![ctx,rawCons a.dom a.cod,a.fn,b.fn]
  have args : ∀ i, D B Γ (programGraph (input i) (results i) xs) := by
    intro i
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c => ?_) b) a) i
    · exact projectionValue 0 xs
    · exact label
    · exact af
    · obtain rfl := Fin.eq_zero c
      exact bf
  exact ⟨fun h => compositionRecover E input (suc z) xs results h args,
    fun h => compositionValue E input (suc z) xs results h args⟩

theorem exact_OpenArgumentChildEdge (E : Program 4) (ctx ty : OTerm α) (a b : AuxRow α) :
    let xs : Fin 4 → OTerm α := ![ctx,ty,a.term,b.term]
    (D B Γ (programGraph (argumentChildEdge E) (suc z) xs) →
      D B Γ (acceptEdge E ctx a.dom a.arg b.arg)) ∧
    (D B Γ (acceptEdge E ctx a.dom a.arg b.arg) →
      D B Γ (programGraph (argumentChildEdge E) (suc z) xs)) := by
  intro xs
  obtain ⟨_,fa⟩ := termReports (body := B) (Γ := Γ) a.dom a.cod a.fn a.arg
  obtain ⟨_,fb⟩ := termReports (body := B) (Γ := Γ) b.dom b.cod b.fn b.arg
  have ad := exact_OpenEdgeSlotRead (field 0) 2 xs a.dom fa.1
  have au := exact_OpenEdgeSlotRead (field 3) 2 xs a.arg fa.2.2.2.1
  have bu := exact_OpenEdgeSlotRead (field 3) 3 xs b.arg fb.2.2.2.1
  let input : Fin 4 → Program 4 := ![.projection 0,fieldSlot 2 0,fieldSlot 2 3,fieldSlot 3 3]
  let results : Fin 4 → OTerm α := ![ctx,a.dom,a.arg,b.arg]
  have args : ∀ i, D B Γ (programGraph (input i) (results i) xs) := by
    intro i
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c => ?_) b) a) i
    · exact projectionValue 0 xs
    · exact ad
    · exact au
    · obtain rfl := Fin.eq_zero c
      exact bu
  exact ⟨fun h => compositionRecover E input (suc z) xs results h args,
    fun h => compositionValue E input (suc z) xs results h args⟩

#print axioms exact_OpenEdgeSlotRead
#print axioms exact_OpenEdgeFieldMatch
#print axioms exact_OpenFunctionChildEdge
#print axioms exact_OpenArgumentChildEdge
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof
