module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepWrapperTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.SelectedNilTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The ACTUAL original parameterized selected step checker has the same
arbitrary output as its old leaf when the ORIGINAL certificate path is nil.
All original source/target/certificate/parameter terms stay unchanged. -/
def OriginalSelectedNilCertificate : Prop :=
 ∀ (endpoint : Program 6) (oldChecker : Program 4)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (out s t cert parameter : OTerm alpha),
 Nonempty (Derivation body Delta
  ((graph1 InternalUnpair.left z cert).imp
   ((graph4 (InternalParameterizedApplicationStepChecker.checkerP endpoint oldChecker)
      out s t cert parameter).iff
    (graph4 oldChecker out s t cert parameter))))

/-- A genuine original variable/bottom certificate reaches the ACTUAL
selectedChecker rather than stopping at its raw closed leaf. Source validity
and literal constructors are the original rule premises; no oldChecker value,
normalizer equation, guard-success or transformed acceptance is assumed. -/
def OriginalSelectedClosedVariable : Prop :=
 ∀ (data : InternalOriginalUniformDescentSelection.Data)
 (source : Program 2) (oldStep : Program 4) (endpoint : Program 6) (window : Program 1)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter typ : OTerm alpha),
 Nonempty (Derivation body Delta
  ((graph2 source (suc z) s parameter ⊓
    (graph1 OriginalLambdaConstructor.tag z s ⊓
     (graph1 InternalUnpair.left typ s ⊓
      (graph1 BottomRepresentative.bottomCode t typ ⊓
       graph1 OriginalTransparentVariableStep.certificateCode cert s)))).imp
   (graph4 (InternalOriginalUniformApplicationStepSelection.selectedChecker data
    (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
     (OriginalTransparentVariableStep.refined source oldStep)))
    (suc z) s t cert parameter)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.SelectedNilTargets
