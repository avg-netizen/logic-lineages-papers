module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalApplicationInversionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalParameterizedCanonicalResultFold

/-- Actual internally recovered application children, their certified fold
outputs and the original reconstructed application. The final selected leaf
graph is retained explicitly; it is not identified with the rebuilt input. -/
def Recovered {alpha : Type} (data : Data)
    (arrow d e fp ap fn arg functionOut argumentOut rebuilt input out parameter : OTerm alpha) : Formula alpha :=
  InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg input ⊓
    (graph2 data.member InternalOriginalStepGuard.one e parameter ⊓
      (certifiedOutput data functionOut fn arrow parameter ⊓
        (certifiedOutput data argumentOut arg d parameter ⊓
          (graph4 application rebuilt d e functionOut argumentOut ⊓
            (sourcePremises data rebuilt e parameter ⊓
              graph2 (leaf data) out rebuilt parameter)))))

/-- Full original application-fold inversion from parent source validity,
its actual application tag, and the actual output alone. All child outputs,
constructor witnesses and guards are recovered internally; body, context,
parameter and Data remain arbitrary. No window or calibration is assumed. -/
def ActualOriginalCanonicalApplicationElimination : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (alpha : Type)
    (Delta : List (Formula alpha)) (input out parameter : OTerm alpha) (psi : Formula alpha),
  Nonempty (Derivation body Delta (graph2 (validity data) InternalOriginalStepGuard.one input parameter)) →
  Nonempty (Derivation body Delta (OriginalConstructorShape.tagGraph positionTerm input)) →
  Nonempty (Derivation body Delta (foldGraph data out input parameter)) →
  (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
    (∀ h ∈ Delta, h.relabel j ∈ Theta) →
    ∀ arrow d e fp ap fn arg functionOut argumentOut rebuilt : OTerm beta,
    Nonempty (Derivation body Theta
      (Recovered data arrow d e fp ap fn arg functionOut argumentOut rebuilt
        (input.relabel j) (out.relabel j) (parameter.relabel j))) →
    Nonempty (Derivation body Theta (psi.relabel j))) →
  Nonempty (Derivation body Delta psi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalApplicationInversionTargets
