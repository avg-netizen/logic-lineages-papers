module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors OriginalNeutralApplication
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact original actualJ equation at the SAME final sidecar-refined data.
The requested function is used directly. A supplied actual argument-fold
graph identifies the argument coordinate; the final eliminator below binds
that output internally. No N(function)=function hypothesis is added. -/
def ActualOriginalTypedApplicationEquation : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (window : Program 1)
    (alpha : Type) (Gamma : List (Formula alpha))
    (arrow d e function argument out argumentOut parameter : OTerm alpha),
  let after := OriginalApplicationSidecar.selectedData data window
  Nonempty (Derivation body Gamma
    ((InputPremises after window arrow d e function argument parameter ⊓
      InternalParameterizedCanonicalResultFold.foldGraph after argumentOut argument parameter).imp
      ((InternalParameterizedCanonicalResultFold.applicationGraph
          after out d e function argument parameter).iff
        (graph4 application out d e function argumentOut))))

/-- Eliminate the supplied actualJ graph using only the original input
premises. Program totality binds the actual full-fold argument internally.
The requested function, raw argument, output, types and parameter are
transported literally through every continuation. No caller-supplied fold
graph, canonical argument, function fixedness or native reflection is used. -/
def ActualOriginalTypedApplicationElimination : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (window : Program 1)
    (alpha : Type) (Gamma : List (Formula alpha))
    (arrow d e function argument out parameter : OTerm alpha) (psi : Formula alpha),
  let after := OriginalApplicationSidecar.selectedData data window
  Nonempty (Derivation body Gamma
    (InputPremises after window arrow d e function argument parameter)) →
  Nonempty (Derivation body Gamma
    (InternalParameterizedCanonicalResultFold.applicationGraph
      after out d e function argument parameter)) →
  (∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)),
    (∀ h ∈ Gamma, h.relabel j ∈ Delta) →
    ∀ argumentOut : OTerm beta,
    Nonempty (Derivation body Delta
      (Recovered after (d.relabel j) (e.relabel j) (function.relabel j)
        (argument.relabel j) (out.relabel j) argumentOut (parameter.relabel j))) →
    Nonempty (Derivation body Delta (psi.relabel j))) →
  Nonempty (Derivation body Gamma psi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationTargets
