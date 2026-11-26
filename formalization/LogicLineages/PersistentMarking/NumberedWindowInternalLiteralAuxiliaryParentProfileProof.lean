module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralChildGuardEdgeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAuxShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxiliaryParentProfileProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons unary)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (termReports onTape)
open NumberedWindowInternalLiteralAuxFallback (sourceIsAux)
open NumberedWindowInternalLiteralAtomicAuxShapeProof (exact_OpenAuxiliaryNotAtoms)
open NumberedWindowInternalLiteralAtomicRawGuardProof (freeTest bottomTest)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (atomicTest)
open NumberedWindowInternalLiteralAtomOnEdgeProof (atomObserver exact_OpenAtomStampZero exact_OpenAtomObserverIntro)
open NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof (AuxRow)
open NumberedWindowInternalLiteralAuxProfileLeastProof (functionHead)
open NumberedWindowInternalLiteralAuxProfileObserversProof
open NumberedWindowInternalLiteralRoundObserverTargets (observe)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D exact_OpenEnrichedEdgeIntro)
open NumberedWindowInternalLiteralChildGuardEdgeProof (childGuardObservers)
open NumberedWindowInternalLiteralEdgeObserversProof (withObservers)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem tagSix (a : AuxRow α) : D B Γ (unary cellHead (numeral 6) a.term) := by
  let row := rawCons a.dom (rawCons a.cod (rawCons a.fn (rawCons a.arg z)))
  obtain ⟨fields⟩ := canonicalCell (body := B) (Γ := Γ) (numeral 6) row
  exact ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight fields)⟩

private theorem atomSix (ctx ty : OTerm α) (a : AuxRow α) : D B Γ (observe atomObserver ctx ty a.term z) := by
  obtain ⟨shape,_⟩ := termReports (body := B) (Γ := Γ) a.dom a.cod a.fn a.arg
  have tapped : D B Γ (programGraph sourceIsAux (suc z) ![a.term,z,z]) :=
    onTape termShape 0 (suc z) ![a.term,z,z] shape
  obtain ⟨atoms⟩ := exact_OpenAuxiliaryNotAtoms a.term z z tapped
  have zero : D B Γ (unary atomicTest z a.term) :=
    zeroBranchIntro freeTest bottomTest (literal 1 1) z ![a.term]
      ⟨Derivation.conjunctionLeft atoms⟩ ⟨Derivation.conjunctionRight atoms⟩
  exact exact_OpenAtomObserverIntro ctx ty a.term z (exact_OpenAtomStampZero a.term zero)

private theorem masked (p : Program 1) (ctx ty q v : OTerm α)
    (shape : D B Γ (unary termShape (suc z) q)) (seen : D B Γ (unary p v q)) :
    D B Γ (observe (unaryObserver (maskedCoordinate p)) ctx ty q v) :=
  exact_OpenUnaryObserverIntro (maskedCoordinate p) ctx ty q v
    (exact_OpenMaskedCoordinateIntro p q z v shape seen)

private theorem fromChildHeader (a : AuxRow α) (h : OTerm α)
    (plane : D B Γ (unary (field 2) a.fn a.term))
    (child : D B Γ (unary cellHead h a.fn)) : D B Γ (unary functionHead h a.term) := by
  apply compositionValue cellHead (Fin.cons (field 2) Fin.elim0) h ![a.term] ![a.fn] child
  intro j
  obtain rfl := Fin.eq_zero j
  exact plane

/-- All six physical child guards can be installed on two literal
auxiliary parents of the same type and with a shared actual function
head. No checker equality or numerical exchange theorem is involved. -/
theorem exact_OpenAuxiliaryParentProfile (ctx ty dom cod f g a b h : OTerm α)
    (first : D B Γ (unary cellHead h f)) (second : D B Γ (unary cellHead h g)) :
    let left : AuxRow α := ⟨dom,cod,f,a⟩
    let right : AuxRow α := ⟨dom,cod,g,b⟩
    ∀ O ∈ childGuardObservers, ∃ v : OTerm α,
      D B Γ (observe O ctx ty left.term v) ∧ D B Γ (observe O ctx ty right.term v) := by
  intro l r O mem
  obtain ⟨shapeL,fieldsL⟩ := termReports (body := B) (Γ := Γ) dom cod f a
  obtain ⟨shapeR,fieldsR⟩ := termReports (body := B) (Γ := Γ) dom cod g b
  simp only [childGuardObservers,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨numeral 6,exact_OpenUnaryObserverIntro cellHead ctx ty l.term (numeral 6) (tagSix l),
      exact_OpenUnaryObserverIntro cellHead ctx ty r.term (numeral 6) (tagSix r)⟩
  · exact ⟨z,atomSix ctx ty l,atomSix ctx ty r⟩
  · exact ⟨suc z,exact_OpenUnaryObserverIntro termShape ctx ty l.term (suc z) shapeL,
      exact_OpenUnaryObserverIntro termShape ctx ty r.term (suc z) shapeR⟩
  · exact ⟨dom,masked (field 0) ctx ty l.term dom shapeL fieldsL.1,
      masked (field 0) ctx ty r.term dom shapeR fieldsR.1⟩
  · exact ⟨cod,masked (field 1) ctx ty l.term cod shapeL fieldsL.2.1,
      masked (field 1) ctx ty r.term cod shapeR fieldsR.2.1⟩
  · exact ⟨h,masked functionHead ctx ty l.term h shapeL (fromChildHeader l h fieldsL.2.2.1 first),
      masked functionHead ctx ty r.term h shapeR (fromChildHeader r h fieldsR.2.2.1 second)⟩

theorem exact_OpenInstallObserverSuite (E : Program 4) (O : List (Program 3)) (ctx ty q r : OTerm α)
    (edge : D B Γ (acceptEdge E ctx ty q r))
    (shared : ∀ P ∈ O, ∃ v : OTerm α, D B Γ (observe P ctx ty q v) ∧ D B Γ (observe P ctx ty r v)) :
    D B Γ (acceptEdge (withObservers E O) ctx ty q r) := by
  induction O with
  | nil => exact edge
  | cons p more ih =>
    obtain ⟨v,a,b⟩ := shared p List.mem_cons_self
    exact exact_OpenEnrichedEdgeIntro (withObservers E more) p ctx ty q r v v
      (ih (fun k h => shared k (List.mem_cons_of_mem _ h))) a b ⟨refl v⟩

#print axioms exact_OpenAuxiliaryParentProfile
#print axioms exact_OpenInstallObserverSuite
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxiliaryParentProfileProof
