module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnObserverProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedEdgeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHeaderLeastGuardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHeaderOnEdgeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalitySelf)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowScalarAlgorithm (Settings edge)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseScalarEdge (packedEdge edge4)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalSparseScalarEdgeNumericProof (calibration)
open NumberedWindowInternalSparseDirectedRoundsTargets (exactEdgeBit)
open NumberedWindowInternalLiteralEnrichedEdgeProof (enrichedEdge exact_EnrichedEdgeBit exact_OpenEnrichedEdgeObservation D)
open NumberedWindowInternalLiteralRoundObserverTargets (observe)
open NumberedWindowInternalLiteralPackedLeastOnProof
open NumberedWindowInternalLiteralLeastOnObserverProof (exact_OpenLiteralSelectedObserverOn)
open NumberedWindowInternalLiteralLeastHeaderInvarianceProof (exact_LiteralScalarEdgeCellHead)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast inputHead outputHead sameHeader allowedOutput)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (outRaw)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (outReport)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- This reads the original header on the third slot, without using the
context or type as a replacement witness for the raw cell. -/
def headerObserver : Program 3 := .composition cellHead (Fin.cons (.projection 2) Fin.elim0)

def headerEdge (X : Program 2) (W : Program 3) : Program 4 := enrichedEdge (edge4 X W) headerObserver

theorem exact_LiteralHeaderEdge (s : Settings) (X : Program 2) (W : Program 3)
    (xFit : ActualTermExchange s X) (wFit : ActualPackedWindow s W) :
    ActualPackedEdgeOn s (headerEdge X W) := by
  unfold ActualPackedEdgeOn headerEdge
  rw [exact_EnrichedEdgeBit]
  · exact exact_OriginalPackedEdgeOn s X W xFit wFit
  · intro ctx ty a b held
    have evaluated := calibration s X W xFit wFit ctx ty a b
    unfold exactEdgeBit at held
    rw [evaluated] at held
    cases decoded : unpack ctx with
    | none =>
      simp [packedEdge,decoded] at held
    | some g =>
      have yes : edge s g ty a b = true := by
        simpa [packedEdge,decoded] using held
      change run cellHead a = run cellHead b
      exact exact_LiteralScalarEdgeCellHead s g ty a b yes

theorem exact_OpenHeaderObserverIntro (ctx ty q h : OTerm α)
    (head : D B Γ (programGraph cellHead h ![q])) :
    D B Γ (observe headerObserver ctx ty q h) := by
  apply compositionValue cellHead (Fin.cons (.projection 2) Fin.elim0) h ![ctx,ty,q] ![q] head
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 2 ![ctx,ty,q]

theorem exact_OpenHeaderObserverElim (ctx ty q h : OTerm α)
    (head : D B Γ (observe headerObserver ctx ty q h)) :
    D B Γ (programGraph cellHead h ![q]) := by
  apply compositionRecover cellHead (Fin.cons (.projection 2) Fin.elim0) h ![ctx,ty,q] ![q] head
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 2 ![ctx,ty,q]

theorem exact_OpenHeaderLeastIntro (L : Program 3) (ctx ty q k head : OTerm α)
    (report : D B Γ (programGraph L (suc k) ![ctx,ty,q]))
    (left : D B Γ (programGraph cellHead head ![q]))
    (right : D B Γ (programGraph cellHead head ![k])) :
    D B Γ (programGraph (headerLeast L) (suc k) ![ctx,ty,q]) := by
  let xs : Fin 2 → OTerm α := ![q,suc k]
  have ih : D B Γ (programGraph inputHead head xs) := by
    apply compositionValue cellHead (Fin.cons (.projection 0) Fin.elim0) head xs ![q] left
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 0 xs
  have oh : D B Γ (programGraph outputHead head xs) := by
    apply compositionValue cellHead (Fin.cons outRaw Fin.elim0) head xs ![k] right
    intro i
    obtain rfl := Fin.eq_zero i
    exact outReport q k
  have eq : D B Γ (programGraph sameHeader (suc z) xs) := by
    unfold sameHeader
    rw [exact_DispatchControlAST.2.2.2.1]
    apply compositionValue equalityTest (Fin.cons inputHead (Fin.cons outputHead Fin.elim0))
      (suc z) xs (Fin.cons head (Fin.cons head Fin.elim0)) (equalitySelf head)
    exact fun i => Fin.cases ih (Fin.cases oh (fun impossible => Fin.elim0 impossible)) i
  have keep := successorBranchIntro sameHeader (constantZero 2) (.projection 1) (suc k) z xs eq
    (projectionValue 1 xs)
  apply compositionValue allowedOutput (Fin.cons (.projection 2) (Fin.cons L Fin.elim0)) (suc k)
    ![ctx,ty,q] xs keep
  exact fun i => Fin.cases (projectionValue 2 ![ctx,ty,q]) (Fin.cases report (fun impossible => Fin.elim0 impossible)) i

/-- The actual selected least can be reinstalled underneath the literal
header guard. The second physical header witness comes out of the
same actual rounds, not from numeric least agreement. -/
theorem exact_OpenHeaderLeastOnEdge (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty q k h : OTerm α)
    (report : D B Γ (leastOnGraph C (headerEdge X W) s ctx ty q k))
    (head : D B Γ (programGraph cellHead h ![q])) :
    D B Γ (programGraph (headerLeast (packedLeastOn C (headerEdge X W) s)) (suc k) ![ctx,ty,q]) := by
  have preserved := exact_OpenEnrichedEdgeObservation (edge4 X W) headerObserver
  have got := exact_OpenLiteralSelectedObserverOn C (headerEdge X W) s headerObserver preserved
    ctx ty q k h report (exact_OpenHeaderObserverIntro ctx ty q h head)
  exact exact_OpenHeaderLeastIntro _ ctx ty q k h report head (exact_OpenHeaderObserverElim ctx ty k h got)

#print axioms exact_LiteralHeaderEdge
#print axioms exact_OpenHeaderObserverIntro
#print axioms exact_OpenHeaderObserverElim
#print axioms exact_OpenHeaderLeastIntro
#print axioms exact_OpenHeaderLeastOnEdge
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHeaderOnEdgeProof
