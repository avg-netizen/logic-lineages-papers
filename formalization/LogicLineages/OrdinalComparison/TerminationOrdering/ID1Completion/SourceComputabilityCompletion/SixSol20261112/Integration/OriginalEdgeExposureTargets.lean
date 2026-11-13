module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PositiveSourceExposureTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalEdgeExposureTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral existsOne)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Bind the ORIGINAL positive certificate before its eleven actual raw-step
witnesses. The original checker acceptance is retained at that same path. -/
def Matrix {alpha : Type} (q : GlobalSourcePackage.Inputs) (context : Nat)
    (source target : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  InternalAccessibilityRules.certificate (GlobalSourcePackage.source q) false context
      (source.relabel Sum.inl) (target.relabel Sum.inl) (.var (.inr 0)) ⊓
    Erasure.PositiveSourceExposureTargets.Witness q context
      (source.relabel Sum.inl) (target.relabel Sum.inl) (.var (.inr 0))

def Witness {alpha : Type} (q : GlobalSourcePackage.Inputs) (context : Nat)
    (source target : OTerm alpha) : Formula alpha :=
  existsOne (Matrix q context source target)

/-- The actual original R-edge used in I-unfolding, with no certificate term
or raw decomposition supplied. All twelve witnesses are bound internally. -/
def ActualOriginalEdgeFirstRawStep : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (context : Nat) (source target : OTerm alpha),
  let q := preparedKernelFinalInputs p H G W P
  Nonempty (Derivation body Delta
    ((graph1 q.window (numeral 1) (numeral context) ⊓
      InternalAccessibilityRules.edge (GlobalSourcePackage.source q) false context source target).imp
      (Witness q context source target)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalEdgeExposureTargets
