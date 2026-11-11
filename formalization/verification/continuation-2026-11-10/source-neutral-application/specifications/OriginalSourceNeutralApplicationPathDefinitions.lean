module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPathDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPath
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedLeastCodeRepresentative (typeNumber)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Retain the original Object application, non-lambda premise and positive
source certificate, with all runtime coordinates exposed internally. The
source's certificate is exactly H+, and its raw path uses that SAME witness
and parameter. Target Gamma equality is derived from the original source. -/
def PathInputs {alpha : Type} (data : Data) (window : Program 1) (oldStep : Program 4)
    (src : SourcePresentation.Data) (comp : JointGammaComputability.Data)
    (context : Nat) (sigma tau : Ty)
    (F A X Y witness gammaCode function argument x y parameter : OTerm alpha) : Formula alpha :=
  OriginalSourceNeutralApplication.Recovered data window comp context sigma tau
      F A X gammaCode function argument x parameter ⊓
    (OriginalSourceNeutralApplication.nonLambdaObject F ⊓
      (OriginalNonLambdaApplication.nonLambda function ⊓
        (InternalAccessibilityRules.certificate src false context X Y witness ⊓
          (graph2 InternalPairing.pairing Y gammaCode y ⊓
            InternalParameterizedPathChecker.positiveGraph (edgeChecker data oldStep)
              x y witness parameter))))

/-- The complete original source inputs and the exact first entry of their
positive path. The remaining ordinary path still reaches the requested
Object endpoint. No constructor shape is imposed on that final endpoint. -/
def RecoveredPrefix {alpha : Type} (data : Data) (window : Program 1) (oldStep : Program 4)
    (src : SourcePresentation.Data) (comp : JointGammaComputability.Data)
    (context : Nat) (sigma tau : Ty)
    (F A X Y witness gammaCode function argument x y parameter raw tail vertex certificate :
      OTerm alpha) : Formula alpha :=
  PathInputs data window oldStep src comp context sigma tau
      F A X Y witness gammaCode function argument x y parameter ⊓
    OriginalNonLambdaApplicationPath.FirstStep data oldStep x y witness parameter
      raw tail vertex certificate

/-- An original non-lambda Object application and its accepted H+ source
certificate supply a classified FIRST edge, retaining every original input,
raw argument, code constructor and the exact reflexive suffix. Both cases
are continuations in the original source calculus at the SAME tuple. -/
def SourcePositivePaths (data : Data) (window : Program 1) (oldStep : Program 4)
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
      (RecoveredPrefix data window oldStep src comp context sigma tau
        (F.relabel j) (A.relabel j) (X.relabel j) (Y.relabel j) (witness.relabel j)
        gammaCode function argument x y parameter raw tail vertex certificate)) →
    Nonempty (Derivation (SourcePresentation.sourceBody src context)
      (graph1 BottomRepresentative.bottomCode vertex (numeral (typeNumber tau)) :: Delta)
      (psi.relabel j))) →
  (∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)),
    (∀ h ∈ Gamma, h.relabel j ∈ Delta) →
    ∀ gammaCode function argument x y parameter raw tail vertex certificate : OTerm beta,
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
      (RecoveredPrefix data window oldStep src comp context sigma tau
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
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta (psi.relabel j))) →
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma psi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPath
