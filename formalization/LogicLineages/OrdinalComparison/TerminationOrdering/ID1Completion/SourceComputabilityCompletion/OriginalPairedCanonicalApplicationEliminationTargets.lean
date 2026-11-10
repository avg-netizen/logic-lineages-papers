module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalApplicationInversionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPairedCanonicalApplicationEliminationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar InternalApplicationCertificateConstructors
open OriginalCanonicalApplicationInversionTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Both original recovered records are retained in full, together with the
proved equalities of domains, codomains and actual canonical child outputs.
No equality of original raw children or rebuilt inputs is asserted. -/
def PairedRecovered {alpha : Type} (data : Data)
    (arrow d e fp ap fn arg functionOut argumentOut rebuilt
      arrow' d' e' fp' ap' fn' arg' functionOut' argumentOut' rebuilt'
      input input' out parameter : OTerm alpha) : Formula alpha :=
  Recovered data arrow d e fp ap fn arg functionOut argumentOut rebuilt input out parameter ⊓
    (Recovered data arrow' d' e' fp' ap' fn' arg' functionOut' argumentOut' rebuilt' input' out parameter ⊓
      (equal d d' ⊓ (equal e e' ⊓
        (equal functionOut functionOut' ⊓ equal argumentOut argumentOut'))))

/-- Continuation-style inversion from just two original valid, application-
tagged sources with a common actual final canonical output. Constructors,
certified children and rebuilt applications are all bound internally. The
window and symbolic parameter belong to the SAME selected final Data. -/
def ActualOriginalPairedCanonicalApplicationElimination : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (window : Program 1)
    (alpha : Type) (Delta : List (Formula alpha))
    (input input' out parameter : OTerm alpha) (psi : Formula alpha),
  let after := selectedData data window
  Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)) →
  Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input' parameter)) →
  Nonempty (Derivation body Delta
    (graph2 (InternalOriginalUniformDescentSelection.validity after) InternalOriginalStepGuard.one input parameter)) →
  Nonempty (Derivation body Delta
    (graph2 (InternalOriginalUniformDescentSelection.validity after) InternalOriginalStepGuard.one input' parameter)) →
  Nonempty (Derivation body Delta (OriginalConstructorShape.tagGraph positionTerm input)) →
  Nonempty (Derivation body Delta (OriginalConstructorShape.tagGraph positionTerm input')) →
  Nonempty (Derivation body Delta (InternalParameterizedCanonicalResultFold.foldGraph after out input parameter)) →
  Nonempty (Derivation body Delta (InternalParameterizedCanonicalResultFold.foldGraph after out input' parameter)) →
  (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
    (∀ h ∈ Delta, h.relabel j ∈ Theta) →
    ∀ arrow d e fp ap fn arg functionOut argumentOut rebuilt
      arrow' d' e' fp' ap' fn' arg' functionOut' argumentOut' rebuilt' : OTerm beta,
    Nonempty (Derivation body Theta
      (PairedRecovered after arrow d e fp ap fn arg functionOut argumentOut rebuilt
        arrow' d' e' fp' ap' fn' arg' functionOut' argumentOut' rebuilt'
        (input.relabel j) (input'.relabel j) (out.relabel j) (parameter.relabel j))) →
    Nonempty (Derivation body Theta (psi.relabel j))) →
  Nonempty (Derivation body Delta psi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPairedCanonicalApplicationEliminationTargets
