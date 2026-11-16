module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.InputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ParameterTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (queryCases)
open InputProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def innerQuery : Program 6 := pairOf (.projection 4) (.projection 5)
def middleQuery : Program 6 := pairOf (.projection 3) innerQuery

theorem transport (xs ys : Fin 6 → OTerm alpha) (param : OTerm alpha)
    (h2 : xs 2 = ys 2) (h3 : xs 3 = ys 3) (h4 : xs 4 = ys 4) (h5 : xs 5 = ys 5)
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs))) :
    Nonempty (Derivation body Delta (programGraph parameterQuery param ys)) := by
  apply queryCases ![innerQuery,middleQuery] xs _
  intro beta j vs Theta hj hq
  rw [programRename]
  have hi : Nonempty (Derivation body Theta (programGraph innerQuery (vs 0) (fun i => (xs i).relabel j))) := by
    simpa using hq 0
  have hm : Nonempty (Derivation body Theta (programGraph middleQuery (vs 1) (fun i => (xs i).relabel j))) := by
    simpa using hq 1
  have hpj := renameInto hp j Theta hj
  rw [programRename] at hpj
  have hip := binaryRecover InternalPairing.pairing (.projection 4) (.projection 5) (vs 0) ((xs 4).relabel j) ((xs 5).relabel j)
    (fun i => (xs i).relabel j) hi (projectionValue 4 _) (projectionValue 5 _)
  have hmp := binaryRecover InternalPairing.pairing (.projection 3) innerQuery (vs 1) ((xs 3).relabel j) (vs 0)
    (fun i => (xs i).relabel j) hm (projectionValue 3 _) hi
  have hpp := binaryRecover InternalPairing.pairing (.projection 2) middleQuery (param.relabel j) ((xs 2).relabel j) (vs 1)
    (fun i => (xs i).relabel j) hpj (projectionValue 2 _) hm
  rw [h4,h5] at hip
  rw [h3] at hmp
  rw [h2] at hpp
  exact parameterValue (fun i => (ys i).relabel j) (vs 0) (vs 1) (param.relabel j) hip hmp hpp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ParameterTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ParameterTransportProof
