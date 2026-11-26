module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMixedLeastProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralChildGuardEdgeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeIntroProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxObserversProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralClassGuardOnProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHeaderLeastOpenProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedRecursiveClassesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration)
open NumberedWindowInternalLiteralCoveredMemo (WindowSeedsCovered)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast atomOutput exact_LiteralAtomicGuardedLeast)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D exact_OpenAtomicLeastReport)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast allowedOutput exact_LiteralHeaderLeast)
open NumberedWindowInternalLiteralHeaderLeastOpenProof (exact_OpenLiteralHeaderLeastReport)
open NumberedWindowInternalLiteralGuardedSelfLeastProof (exact_OpenLiteralGuardedSelfLeast)
open NumberedWindowInternalLiteralAuxProfileLeastProof (auxProfileLeast exact_LiteralAuxProfileLeast)
open NumberedWindowInternalLiteralAuxProfileLeastOpenProof (exact_OpenLiteralAuxProfileLeastReport)
open NumberedWindowInternalLiteralAuxProfileSelfProof (exact_OpenLiteralAuxProfileSelfLeast)
open NumberedWindowInternalLiteralAuxClassLeastProof
open NumberedWindowInternalLiteralAuxClassLeastOpenProof (exact_OpenLiteralAuxClassLeastReport)
open NumberedWindowInternalLiteralAuxClassSharedProof (exact_OpenLiteralAuxClassSelfLeast)
open NumberedWindowInternalLiteralApplicationLeastDecoratorProof (OpenDecorator)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof (childGuardedLeast fullAuxiliaryDecorator)
open NumberedWindowInternalLiteralTypedMixedLeastProof (mixedFilteredLeast)
open NumberedWindowInternalLiteralClassObserverProof (classObserver)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalLiteralChildGuardEdgeProof
open NumberedWindowInternalLiteralClassGuardOnProof
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn leastOnGraph)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralAuxProfileObserversProof (unaryObserver)
open NumberedWindowInternalLiteralTypedAuxEdgeGuardProof (typedAuxEdgeGuard)
open NumberedWindowInternalLiteralTypedAuxEdgeIntroProof (exact_OpenTypedAuxEdgeBase)
open NumberedWindowInternalLiteralTypedAuxObserversProof


/-- A physical refinement, unlike equality of numerical evaluations, gives
an object derivation in the same body and context for every selected edge. -/
def TypedEdgeRefines (G H : Program 4) : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty q r : OTerm α),
    D B Γ (acceptEdge G ctx ty q r) → D B Γ (acceptEdge H ctx ty q r)

theorem exact_OpenTypedObserverRefines (G H : Program 4) (O : Program 3)
    (refines : TypedEdgeRefines G H) (stable : Preserves H O) : Preserves G O := by
  intro B α Γ ctx ty q r value edge read
  exact stable B α Γ ctx ty q r value (refines B α Γ ctx ty q r edge) read

/-- The proof does not define an AST recursively. It specifies the exact
physical unfolding law that a finite memoized implementation must supply
in order to compare classes using its own least program. -/
theorem exact_OpenTypedRecursiveClassObservers (Base G : Program 4) (K : Program 3)
    (unfolding : TypedEdgeRefines G (typedAuxEdgeGuard Base G))
    (shape : Preserves Base (unaryObserver termShape)) (stable : Preserves G K) :
    Preserves G (classObserver (functionClass K)) ∧
      Preserves G (classObserver (argumentClass K)) :=
  ⟨exact_OpenTypedObserverRefines G _ _ unfolding (exact_OpenTypedFunctionClassObserver Base G K shape stable),
    exact_OpenTypedObserverRefines G _ _ unfolding (exact_OpenTypedArgumentClassObserver Base G K shape stable)⟩

/-- Class preference may be installed on the original production rounds as
soon as both class observers physically move with those rounds. This includes
nested auxiliary input and does not require a numerical substitution. -/
theorem exact_OpenTypedInstalledClasses (C : Program 3) (G : Program 4) (s : Settings) (K : Program 3)
    (installed : ∀ O ∈ childGuardObservers, Preserves G O)
    (fn : Preserves G (classObserver (functionClass K)))
    (arg : Preserves G (classObserver (argumentClass K)))
    (ctx ty q k : OTerm α) (actual : D B Γ (leastOnGraph C G s ctx ty q k)) :
    D B Γ (programGraph (mixedFilteredLeast K (packedLeastOn C G s)) (suc k) ![ctx,ty,q]) := by
  let L := packedLeastOn C G s
  let middle := classGuardWith K (childGuardedLeast L)
  have test := exact_OpenClassCheckOn C G s K
    (installed (unaryObserver termShape) (by simp [childGuardObservers])) fn arg ctx ty q k actual
  have child := exact_OpenChildGuardLeast C G s installed ctx ty q k actual
  obtain ⟨atom⟩ := exact_OpenAtomicLeastReport (headerLeast (auxProfileLeast L)) ctx ty q k child
  obtain ⟨top⟩ := exact_OpenLiteralHeaderLeastReport (auxProfileLeast L) ctx ty q k ⟨Derivation.conjunctionLeft atom⟩
  have withClass := exact_OpenClassGuardWithIntro K (childGuardedLeast L) ctx ty q k child test
  let xs : Fin 3 → OTerm α := ![ctx,ty,q]
  have withHeader : D B Γ (programGraph (headerLeast middle) (suc k) xs) := by
    apply compositionValue allowedOutput (Fin.cons (.projection 2) (Fin.cons middle Fin.elim0))
      (suc k) xs ![q,suc k] ⟨Derivation.conjunctionRight top⟩
    exact fun i => Fin.cases (projectionValue 2 xs) (Fin.cases withClass (fun n => Fin.elim0 n)) i
  apply compositionValue atomOutput (Fin.cons (.projection 2) (Fin.cons (headerLeast middle) Fin.elim0))
    (suc k) xs ![q,suc k] ⟨Derivation.conjunctionRight atom⟩
  exact fun i => Fin.cases (projectionValue 2 xs) (Fin.cases withHeader (fun n => Fin.elim0 n)) i

/-- Exact diagonal, conditional only on the physical typed unfolding and
the ordinary edge stability of the guarded least selector. Both original
class callbacks now use the very same guarded program which produced the
selected positive result. -/
theorem exact_OpenTypedRecursiveFilteredLeast (C : Program 3) (Base G : Program 4) (s : Settings)
    (unfolding : TypedEdgeRefines G (typedAuxEdgeGuard Base G))
    (guards : ∀ O ∈ childGuardObservers, Preserves Base O)
    (stable : Preserves G (childGuardedLeast (packedLeastOn C G s)))
    (ctx ty q k : OTerm α) (actual : D B Γ (leastOnGraph C G s ctx ty q k)) :
    D B Γ (programGraph (guardedLeast (headerLeast (fullAuxiliaryDecorator (packedLeastOn C G s))))
      (suc k) ![ctx,ty,q]) := by
  have projects : TypedEdgeRefines G Base := by
    intro B α Γ c t a b h
    exact exact_OpenTypedAuxEdgeBase Base G c t a b (unfolding B α Γ c t a b h)
  have original : ∀ O ∈ childGuardObservers, Preserves G O := by
    intro O mem
    exact exact_OpenTypedObserverRefines G Base O projects (guards O mem)
  have shape := guards (unaryObserver termShape) (by simp [childGuardObservers])
  obtain ⟨fn,arg⟩ := exact_OpenTypedRecursiveClassObservers Base G _ unfolding shape stable
  exact exact_OpenTypedInstalledClasses C G s _ original fn arg ctx ty q k actual

#print axioms exact_OpenTypedObserverRefines
#print axioms exact_OpenTypedRecursiveClassObservers
#print axioms exact_OpenTypedInstalledClasses
#print axioms exact_OpenTypedRecursiveFilteredLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedRecursiveClassesProof
