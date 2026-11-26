module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxClassTransportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPositiveBooleanProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralClassObserverProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundObserverSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedEdgeReversalProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxObserversProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalControlGraphSupportProof (valueUnique outputTransport)
open ID1Completion.InternalTagArithmeticSupportProof (symm refl)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim zeroBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (edgeRename)
open NumberedWindowInternalLiteralRoundObserverTargets (observe Preserves)
open NumberedWindowInternalLiteralRoundObserverSyntaxProof (observeRename)
open NumberedWindowInternalLiteralAuxProfileObserversProof
open NumberedWindowInternalLiteralClassObserverProof
open NumberedWindowInternalLiteralPositiveBooleanProof (exact_OpenPositiveAuxShape)
open NumberedWindowInternalLiteralAuxClassLeastProof (functionClass argumentClass)
open NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof (AuxRow)
open NumberedWindowInternalLiteralTypedAuxEdgeOpenProof (childAlternatives)
open NumberedWindowInternalLiteralTypedAuxEdgeGuardProof
open NumberedWindowInternalLiteralTypedAuxEdgeCasesOpenProof
open NumberedWindowInternalLiteralTypedAuxClassTransportProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def OpenTypedClassMove (E : Program 4) (P : Program 2) : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx value : OTerm α)
    (a b : AuxRow α), D B Γ (eqn a.dom b.dom) → D B Γ (eqn a.cod b.cod) →
    D B Γ (childAlternatives E ctx a b) → D B Γ (programGraph P value ![ctx,a.term]) →
    D B Γ (programGraph P value ![ctx,b.term])

private theorem changeRaw (P : Program 2) (ctx q r value : OTerm α)
    (same : D B Γ (eqn q r)) (actual : D B Γ (programGraph P value ![ctx,q])) :
    D B Γ (programGraph P value ![ctx,r]) := by
  unfold programGraph at *
  apply graphInputTransport B α 2 Γ (OrdinaryArithmetic.graphFormula P) value ![ctx,q] ![ctx,r] _ actual
  intro i
  rw [onEquality]
  exact Fin.cases (⟨refl ctx⟩ : D B Γ (eqn ctx ctx)) (Fin.cases same (fun n => Fin.elim0 n)) i

private theorem originalEdge (Base E : Program 4) (ctx ty q r : OTerm α)
    (held : D B Γ (acceptEdge (typedAuxEdgeGuard Base E) ctx ty q r)) :
    D B Γ (acceptEdge Base ctx ty q r) := by
  obtain ⟨actual⟩ := conjunctionRecover Base (auxChildGuard E) ![ctx,ty,q,r] held
  exact ⟨Derivation.conjunctionLeft actual⟩

/-- The physically checked smaller typed disjunction makes the class
of either selected child a stable observer, without adding a
separate class-comparison bit to the outer edge. The proof preserves
all callback outputs, including zero. -/
theorem exact_OpenTypedClassObserver (Base E : Program 4) (P : Program 2)
    (shapeKeep : Preserves Base (unaryObserver termShape)) (move : OpenTypedClassMove E P) :
    Preserves (typedAuxEdgeGuard Base E) (classObserver P) := by
  intro B α Γ ctx ty q r value edge seen
  apply optionGraphCases termShape ![q] _
  · intro β j Δ keep shape
    rw [observeRename]
    rw [unaryInputsRename] at shape
    have e := renameInto edge j Δ keep
    rw [edgeRename] at e
    have v := renameInto seen j Δ keep
    rw [observeRename] at v
    let c := ctx.relabel j
    let t := ty.relabel j
    let a := q.relabel j
    let b := r.relabel j
    let k := value.relabel j
    have start := exact_OpenUnaryObserverIntro termShape c t a z shape
    have gz := shapeKeep B β Δ c t a b z (originalEdge Base E c t a b e) start
    have no := zeroBranchElim (unaryObserver termShape) (constantZero 3) (classRead P)
      k ![c,t,a] start v
    obtain ⟨eq⟩ := valueUnique (constantZero 3) k z ![c,t,a] no (zeroConstantValue ![c,t,a])
    have target : D B Δ (observe (classObserver P) c t b z) :=
      zeroBranchIntro (unaryObserver termShape) (constantZero 3) (classRead P)
        z ![c,t,b] gz (zeroConstantValue ![c,t,b])
    exact outputTransport (classObserver P) z k ![c,t,b] ⟨symm eq⟩ target
  · intro β j Δ event keep active
    rw [observeRename]
    rw [unaryInputsRename] at active
    have e := renameInto edge j Δ keep
    rw [edgeRename] at e
    have v := renameInto seen j Δ keep
    rw [observeRename] at v
    let c := ctx.relabel j
    let t := ty.relabel j
    let a := q.relabel j
    let b := r.relabel j
    let k := value.relabel j
    have positive := exact_OpenPositiveAuxShape a event active
    have targetShape := exact_OpenAuxEdgeTargetShape Base E c t a b e positive
    apply exact_OpenAnyTypedAuxEdgeCases Base E c t a b _ e positive
    intro γ n Θ left right stay eqA eqB facts
    rw [observeRename]
    have earlier := renameInto v n Θ stay
    rw [observeRename] at earlier
    have atA := renameInto positive n Θ stay
    have atB := renameInto targetShape n Θ stay
    simp only [unaryRename,sucRelabel,zRelabel] at atA atB
    let cc := c.relabel n
    let tt := t.relabel n
    let aa := a.relabel n
    let bb := b.relabel n
    let vv := k.relabel n
    have old := exact_OpenActiveClassObserverElim P cc tt aa z vv atA earlier
    have source := changeRaw P cc aa left.term vv eqA old
    obtain ⟨checked⟩ := facts
    have target := move B γ Θ cc vv left right ⟨Derivation.conjunctionLeft checked⟩
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight checked)⟩
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight checked)⟩ source
    obtain ⟨eqB⟩ := eqB
    exact exact_OpenActiveClassObserverIntro P cc tt bb z vv atB
      (changeRaw P cc right.term bb vv ⟨symm eqB⟩ target)

theorem exact_OpenTypedFunctionClassObserver (Base E : Program 4) (K : Program 3)
    (shapeKeep : Preserves Base (unaryObserver termShape)) (stable : Preserves E K) :
    Preserves (typedAuxEdgeGuard Base E) (classObserver (functionClass K)) :=
  exact_OpenTypedClassObserver Base E _ shapeKeep (by
    intro B α Γ ctx value a b dom cod arc source
    exact exact_OpenTypedAuxFunctionClassTransport E K stable ctx value a b dom cod arc source)

theorem exact_OpenTypedArgumentClassObserver (Base E : Program 4) (K : Program 3)
    (shapeKeep : Preserves Base (unaryObserver termShape)) (stable : Preserves E K) :
    Preserves (typedAuxEdgeGuard Base E) (classObserver (argumentClass K)) :=
  exact_OpenTypedClassObserver Base E _ shapeKeep (by
    intro B α Γ ctx value a b dom _ arc source
    exact exact_OpenTypedAuxArgumentClassTransport E K stable ctx value a b dom arc source)

#print axioms exact_OpenTypedClassObserver
#print axioms exact_OpenTypedFunctionClassObserver
#print axioms exact_OpenTypedArgumentClassObserver
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxObserversProof
