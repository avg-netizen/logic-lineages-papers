module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationLeastDecoratorProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralGuardedSelfLeastProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHeaderLeastOpenProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof
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

/-- Every compared child report already includes the actual original
atom, header, and auxiliary profile guards. The outer class stage is
new only at literal auxiliaries. -/
def childGuardedLeast (L : Program 3) : Program 3 :=
  guardedLeast (headerLeast (auxProfileLeast L))

def fullAuxiliaryDecorator (L : Program 3) : Program 3 := auxClassLeast (childGuardedLeast L)

theorem exact_FullAuxiliaryDecoratorOpen : OpenDecorator fullAuxiliaryDecorator := by
  constructor
  · intro L B α Γ c t q k h
    obtain ⟨classes⟩ := exact_OpenLiteralAuxClassLeastReport (childGuardedLeast L) c t q k h
    obtain ⟨atom⟩ := exact_OpenAtomicLeastReport (headerLeast (auxProfileLeast L)) c t q k
      ⟨Derivation.conjunctionLeft classes⟩
    obtain ⟨header⟩ := exact_OpenLiteralHeaderLeastReport (auxProfileLeast L) c t q k
      ⟨Derivation.conjunctionLeft atom⟩
    obtain ⟨original⟩ := exact_OpenLiteralAuxProfileLeastReport L c t q k ⟨Derivation.conjunctionLeft header⟩
    exact ⟨Derivation.conjunctionLeft original⟩
  · intro L B α Γ c t k h
    exact exact_OpenLiteralAuxClassSelfLeast (childGuardedLeast L) c t k
      (exact_OpenLiteralGuardedSelfLeast (auxProfileLeast L) c t k (exact_OpenLiteralAuxProfileSelfLeast L c t k h))

theorem exact_FullAuxiliaryDecoratorCalibration (s : Settings) (cover : WindowSeedsCovered s)
    (symmetric : HeadPairsSymmetric s.equivalentHeads) (L : Program 3) (fit : ActualLeastCalibration s L) :
    ActualLeastCalibration s (fullAuxiliaryDecorator L) :=
  exact_LiteralAuxClassLeast s cover symmetric (childGuardedLeast L)
    (exact_LiteralAtomicGuardedLeast s (headerLeast (auxProfileLeast L))
      (exact_LiteralHeaderLeast s (auxProfileLeast L) (exact_LiteralAuxProfileLeast s L fit)))

/-- In the non-auxiliary branch, the actual child-class guard passes
a positive original report without calling any child selector. -/
theorem exact_OpenAuxClassLeastNonAuxIntro (L : Program 3) (ctx ty q k : OTerm α)
    (shape : D B Γ (unary termShape z q))
    (old : D B Γ (programGraph L (suc k) ![ctx,ty,q])) :
    D B Γ (programGraph (auxClassLeast L) (suc k) ![ctx,ty,q]) := by
  let xs : Fin 3 → OTerm α := ![ctx,q,suc k]
  have no : D B Γ (programGraph selectedAuxiliary z xs) := by
    apply compositionValue termShape (Fin.cons (.projection 1) Fin.elim0) z xs ![q] shape
    intro j
    obtain rfl := Fin.eq_zero j
    exact projectionValue 1 xs
  have test := zeroBranchIntro selectedAuxiliary (constantOne 3) (childClassesAgree L)
    (suc z) xs no (oneConstantValue xs)
  have retained := successorBranchIntro (checkAuxiliaryClasses L) (constantZero 3) (.projection 2)
    (suc k) z xs test (projectionValue 2 xs)
  let input : Fin 3 → OTerm α := ![ctx,ty,q]
  apply compositionValue (retainClasses L) (Fin.cons (.projection 0) (Fin.cons (.projection 2) (Fin.cons L Fin.elim0)))
    (suc k) input xs retained
  exact fun i => Fin.cases (projectionValue 0 input)
    (Fin.cases (projectionValue 2 input) (Fin.cases old (fun n => Fin.elim0 n))) i

/-- The original assembly uses the same physical gate reports from
the already guarded child call. Only the newly selected class guard
has to be introduced, and its actual non-auxiliary control pays it.
Tag-six children are not asserted to follow from this rule. -/
theorem exact_OpenFullFilteredNonAuxLeast (L : Program 3) (ctx ty q k : OTerm α)
    (shape : D B Γ (unary termShape z q))
    (child : D B Γ (programGraph (childGuardedLeast L) (suc k) ![ctx,ty,q])) :
    D B Γ (programGraph (guardedLeast (headerLeast (fullAuxiliaryDecorator L))) (suc k) ![ctx,ty,q]) := by
  let middle := fullAuxiliaryDecorator L
  obtain ⟨atom⟩ := exact_OpenAtomicLeastReport (headerLeast (auxProfileLeast L)) ctx ty q k child
  obtain ⟨top⟩ := exact_OpenLiteralHeaderLeastReport (auxProfileLeast L) ctx ty q k ⟨Derivation.conjunctionLeft atom⟩
  have withClass := exact_OpenAuxClassLeastNonAuxIntro (childGuardedLeast L) ctx ty q k shape child
  let xs : Fin 3 → OTerm α := ![ctx,ty,q]
  have withHeader : D B Γ (programGraph (headerLeast middle) (suc k) xs) := by
    apply compositionValue allowedOutput (Fin.cons (.projection 2) (Fin.cons middle Fin.elim0))
      (suc k) xs ![q,suc k] ⟨Derivation.conjunctionRight top⟩
    exact fun i => Fin.cases (projectionValue 2 xs) (Fin.cases withClass (fun n => Fin.elim0 n)) i
  apply compositionValue atomOutput (Fin.cons (.projection 2) (Fin.cons (headerLeast middle) Fin.elim0))
    (suc k) xs ![q,suc k] ⟨Derivation.conjunctionRight atom⟩
  exact fun i => Fin.cases (projectionValue 2 xs) (Fin.cases withHeader (fun n => Fin.elim0 n)) i

#print axioms exact_FullAuxiliaryDecoratorOpen
#print axioms exact_FullAuxiliaryDecoratorCalibration
#print axioms exact_OpenAuxClassLeastNonAuxIntro
#print axioms exact_OpenFullFilteredNonAuxLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof
