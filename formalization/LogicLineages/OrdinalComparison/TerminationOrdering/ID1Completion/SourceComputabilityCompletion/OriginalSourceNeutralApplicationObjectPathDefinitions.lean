module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPathDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationObjectPath
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedLeastCodeRepresentative (typeNumber)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Retain the complete original source H+ first-entry rule. In its function
case, internally bind the original target-function and first-vertex Objects
at the SAME Gamma and reconstruct the accepted Object application with the
SAME requested argument Object. The original prefix, full aligned quotient
record and unchanged suffix remain explicit. No function-child source
certificate, suffix computability or final-endpoint shape is asserted. -/
def ObjectSourcePositivePaths (data : Data) (window : Program 1) (oldStep : Program 4)
    (src : SourcePresentation.Data) (comp : JointGammaComputability.Data) (context : Nat) : Prop :=
  ∀ (alpha : Type) (Gamma : List (Formula alpha)) (sigma tau : Ty)
    (F A X Y witness : OTerm alpha) (psi : Formula alpha),
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
    (InternalComputabilityDownward.domain comp context sigma tau F A)) →
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
    (InternalComputabilityApplication.accepted comp sigma tau (numeral context) F A X)) →
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
    (OriginalSourceNeutralApplication.nonLambdaObject F)) →
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
    (InternalAccessibilityRules.certificate src false context X Y witness)) →
  (∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)),
    (∀ h ∈ Gamma, h.relabel j ∈ Delta) →
    ∀ gammaCode function argument x y parameter raw tail vertex certificate : OTerm beta,
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
      (OriginalSourceNeutralApplicationPath.RecoveredPrefix data window oldStep src comp context sigma tau
        (F.relabel j) (A.relabel j) (X.relabel j) (Y.relabel j) (witness.relabel j)
        gammaCode function argument x y parameter raw tail vertex certificate)) →
    Nonempty (Derivation (SourcePresentation.sourceBody src context)
      (graph1 BottomRepresentative.bottomCode vertex (numeral (typeNumber tau)) :: Delta)
      (psi.relabel j))) →
  (∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)),
    (∀ h ∈ Gamma, h.relabel j ∈ Delta) →
    ∀ gammaCode function argument x y parameter raw tail vertex certificate : OTerm beta,
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
      (OriginalSourceNeutralApplicationPath.RecoveredPrefix data window oldStep src comp context sigma tau
        (F.relabel j) (A.relabel j) (X.relabel j) (Y.relabel j) (witness.relabel j)
        gammaCode function argument x y parameter raw tail vertex certificate)) →
    ∀ S T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child
      functionOut targetFunctionOut canonicalArgument argumentOut : OTerm beta,
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
      (OriginalNeutralApplicationEdge.Recovered data oldStep
        (numeral (typeNumber (.arrow sigma tau))) (numeral (typeNumber sigma))
        (numeral (typeNumber tau)) function argument x vertex certificate parameter
        S T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child
        functionOut targetFunctionOut canonicalArgument argumentOut)) →
    ∀ targetFunctionObject vertexObject : OTerm beta,
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
      (OriginalSourceApplicationReconstruction.Recovered data window comp context sigma tau
        (F.relabel j) (A.relabel j) (X.relabel j)
        gammaCode function argument x parameter targetFunctionOut vertex
        targetFunctionObject vertexObject)) →
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta (psi.relabel j))) →
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma psi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationObjectPath
