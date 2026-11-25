module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxClassSharedProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileSelfProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationSelectedCarrierProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationLeastDecoratorProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D)
open NumberedWindowInternalLiteralAuxClassLeastProof (auxClassLeast exact_LiteralAuxClassLeast)
open NumberedWindowInternalLiteralAuxProfileLeastProof (auxProfileLeast exact_LiteralAuxProfileLeast)
open NumberedWindowInternalLiteralAuxClassLeastOpenProof (exact_OpenLiteralAuxClassLeastReport)
open NumberedWindowInternalLiteralAuxProfileLeastOpenProof (exact_OpenLiteralAuxProfileLeastReport)
open NumberedWindowInternalLiteralAuxClassSharedProof (exact_OpenLiteralAuxClassSelfLeast)
open NumberedWindowInternalLiteralAuxProfileSelfProof (exact_OpenLiteralAuxProfileSelfLeast)
open NumberedWindowInternalLiteralCoveredMemo (WindowSeedsCovered)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)

attribute [local irreducible] programGraph

/-- Additional tests on a physically selected least must be peeled
on an actual success and reintroduced at an actual self result, on
the same open body. Numeric equivalence alone is not this interface. -/
structure OpenDecorator (decorate : Program 3 → Program 3) : Prop where
  erase : ∀ (L : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
      (ctx ty seed k : OTerm α),
    D B Γ (programGraph (decorate L) (suc k) ![ctx,ty,seed]) →
    D B Γ (programGraph L (suc k) ![ctx,ty,seed])
  self : ∀ (L : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
      (ctx ty k : OTerm α),
    D B Γ (programGraph L (suc k) ![ctx,ty,k]) →
    D B Γ (programGraph (decorate L) (suc k) ![ctx,ty,k])

def auxiliaryDecorator (L : Program 3) : Program 3 := auxClassLeast (auxProfileLeast L)

theorem exact_ApplicationAuxiliaryDecoratorOpen : OpenDecorator auxiliaryDecorator := by
  constructor
  · intro L B α Γ c t q k checked
    obtain ⟨classes⟩ := exact_OpenLiteralAuxClassLeastReport (auxProfileLeast L) c t q k checked
    obtain ⟨profile⟩ := exact_OpenLiteralAuxProfileLeastReport L c t q k
      ⟨Derivation.conjunctionLeft classes⟩
    exact ⟨Derivation.conjunctionLeft profile⟩
  · intro L B α Γ c t k checked
    exact exact_OpenLiteralAuxClassSelfLeast (auxProfileLeast L) c t k
      (exact_OpenLiteralAuxProfileSelfLeast L c t k checked)

theorem exact_ApplicationAuxiliaryDecoratorCalibration (s : Settings)
    (covered : WindowSeedsCovered s) (symmetric : HeadPairsSymmetric s.equivalentHeads)
    (L : Program 3) (cal : ActualLeastCalibration s L) :
    ActualLeastCalibration s (auxiliaryDecorator L) :=
  exact_LiteralAuxClassLeast s covered symmetric (auxProfileLeast L) (exact_LiteralAuxProfileLeast s L cal)

#print axioms exact_ApplicationAuxiliaryDecoratorOpen
#print axioms exact_ApplicationAuxiliaryDecoratorCalibration
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationLeastDecoratorProof
