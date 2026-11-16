module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BinaryResultObservationsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Induction
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)

def maximumProgram : Program 3 := .composition OriginalBoundsRecombination.maximum ![.projection 1,.projection 2]
def pairProgram : Program 3 := .composition InternalPairing.pairing ![.projection 0,maximumProgram]
def queries : Fin 2 → Program 3 := ![maximumProgram,pairProgram]

theorem cases (size leftLabel rightLabel : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (maximum canonical : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 OriginalBoundsRecombination.maximum maximum (leftLabel.relabel j) (rightLabel.relabel j))) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing canonical (size.relabel j) maximum)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases queries ![size,leftLabel,rightLabel] psi
  intro beta j ys Theta hj hq
  have hx : (fun i => (![size,leftLabel,rightLabel] i).relabel j) =
      ![size.relabel j,leftLabel.relabel j,rightLabel.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  let xs : Fin 3 → OTerm beta := ![size.relabel j,leftLabel.relabel j,rightLabel.relabel j]
  have hm : Nonempty (Derivation body Theta (programGraph maximumProgram (ys 0) xs)) := hq 0
  have hp : Nonempty (Derivation body Theta (programGraph pairProgram (ys 1) xs)) := hq 1
  exact next beta j Theta (ys 0) (ys 1) hj
    (binaryRecover OriginalBoundsRecombination.maximum (.projection 1) (.projection 2) (ys 0)
      (leftLabel.relabel j) (rightLabel.relabel j) xs hm (projectionValue 1 xs) (projectionValue 2 xs))
    (binaryRecover InternalPairing.pairing (.projection 0) maximumProgram (ys 1)
      (size.relabel j) (ys 0) xs hp (projectionValue 0 xs) hm)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BinaryResultObservationsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BinaryResultObservationsProof
