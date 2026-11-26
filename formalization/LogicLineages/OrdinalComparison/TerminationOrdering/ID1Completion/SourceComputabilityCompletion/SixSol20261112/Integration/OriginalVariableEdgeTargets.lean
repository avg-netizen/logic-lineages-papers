module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.CorrectedOriginalVariableDichotomyTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalVariableEdgeTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The old source relation is its ORIGINAL existential edge formula; no old
certificate term or recognition fact is supplied to the erasure law. -/
def Premise {alpha : Type} (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) (context : Nat) (tau : Ty)
    (source target gamma extended packed raw domain index : OTerm alpha) : Formula alpha :=
  let f := preparedKernelFinalInputs p H G W P
  graph1 f.window (numeral 1) (numeral context) ⊓
    (InternalComputabilityApplication.typed (GlobalSourcePackage.computability f)
        tau (numeral context) source ⊓
      (OriginalErasureCertificateContinuation.Shape tau source gamma extended packed raw domain index ⊓
        InternalAccessibilityRules.edge (GlobalSourcePackage.source f) false context source target))

def Result {alpha : Type} (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) (context : Nat)
    (source target erasedSource erasedTarget : OTerm alpha) : Formula alpha :=
  (equal erasedSource erasedTarget ⊓
    OriginalVariableErasureCertificate.OriginalRankDrop source target) ⊔
    InternalAccessibilityRules.edge
      (GlobalSourcePackage.source (preparedKernelFinalInputs p H G W P)) false
      context erasedSource erasedTarget

/-- Actual ORIGINAL source-edge erasure at every variable index, preserving
the same final source and the actual Object outputs. This is one rule family
for the original I-closure argument, not unrestricted source erasure. -/
def ActualOriginalVariableEdgeErasure : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (context : Nat) (tau : Ty)
    (source target gamma extended packed raw domain index erasedSource erasedTarget : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Premise p H G W P context tau source target gamma extended packed raw domain index ⊓
      (graph1 OriginalRawObjectTransport.eraseObjectRaw erasedSource source ⊓
        graph1 OriginalRawObjectTransport.eraseObjectRaw erasedTarget target)).imp
      (Result p H G W P context source target erasedSource erasedTarget)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalVariableEdgeTargets
