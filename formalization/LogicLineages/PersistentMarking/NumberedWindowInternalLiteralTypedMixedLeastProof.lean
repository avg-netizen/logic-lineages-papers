module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralChildGuardEdgeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeIntroProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxObserversProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralClassGuardOnProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHeaderLeastOpenProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMixedLeastProof
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

open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof (childGuardedLeast)
open NumberedWindowInternalLiteralChildGuardEdgeProof
open NumberedWindowInternalLiteralClassGuardOnProof
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn leastOnGraph)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralAuxProfileObserversProof (unaryObserver)
open NumberedWindowInternalLiteralTypedAuxEdgeGuardProof (typedAuxEdgeGuard)
open NumberedWindowInternalLiteralTypedAuxEdgeIntroProof (exact_OpenTypedAuxEdgeBase)
open NumberedWindowInternalLiteralTypedAuxObserversProof

/-- Every constituent of the selected positive report is paid by the very
same structurally refined rounds. The class comparator is a separately named
program: stability on the physically read child edge, not numerical
equivalence to the least producer, is its hypothesis. -/
def mixedFilteredLeast (K L : Program 3) : Program 3 :=
  guardedLeast (headerLeast (classGuardWith K (childGuardedLeast L)))

theorem exact_OpenTypedMixedLeast (C : Program 3) (Base E : Program 4)
    (s : Settings) (K : Program 3)
    (checked : ∀ O ∈ childGuardObservers, Preserves Base O)
    (stable : Preserves E K)
    (ctx ty q k : OTerm α)
    (actual : D B Γ (leastOnGraph C (typedAuxEdgeGuard Base E) s ctx ty q k)) :
    D B Γ (programGraph (mixedFilteredLeast K (packedLeastOn C (typedAuxEdgeGuard Base E) s))
      (suc k) ![ctx,ty,q]) := by
  let G := typedAuxEdgeGuard Base E
  let L := packedLeastOn C G s
  let middle := classGuardWith K (childGuardedLeast L)
  have installed : ∀ O ∈ childGuardObservers, Preserves G O := by
    intro O mem B α Γ ctx ty q r v edge read
    exact checked O mem B α Γ ctx ty q r v (exact_OpenTypedAuxEdgeBase Base E ctx ty q r edge) read
  have shape := checked (unaryObserver termShape) (by simp [childGuardObservers])
  have fn := exact_OpenTypedFunctionClassObserver Base E K shape stable
  have arg := exact_OpenTypedArgumentClassObserver Base E K shape stable
  have test := exact_OpenClassCheckOn C G s K (installed (unaryObserver termShape)
    (by simp [childGuardObservers])) fn arg ctx ty q k actual
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

#print axioms exact_OpenTypedMixedLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMixedLeastProof
