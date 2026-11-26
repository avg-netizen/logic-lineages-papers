module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowBumpProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open ID1Completion.InternalUnpair (left right)
open ID1Completion.InternalUnpairProof (actualOriginalGeneratedCodeInverse)
open ID1Completion.InternalPairing (pairing)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue successorValue)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalCoverLambdaMeasureRowTargets

attribute [local irreducible] programGraph

theorem exact_OpenCoverLambdaBumpPair : ExactOpenCoverLambdaBumpPair := by
  intro body α Γ p mc d w child out
  obtain ⟨law⟩ := actualOriginalGeneratedCodeInverse body α mc d w
  obtain ⟨child⟩ := child
  have fields := Derivation.implicationElimination (weakenClosed law Γ) child
  have depth : Nonempty (Derivation body Γ (unary successorDepth (suc d) mc)) := by
    apply compositionValue (.succ : Program 1) (fun _ : Fin 1 => left) (suc d)
      ![mc] ![d] (successorValue ![d])
    intro i
    obtain rfl := Fin.eq_zero i
    exact ⟨Derivation.conjunctionLeft fields⟩
  apply compositionRecover pairing ![successorDepth,right] p ![mc] ![suc d,w] out
  intro i
  exact Fin.cases depth (Fin.cases ⟨Derivation.conjunctionRight fields⟩ (fun j => Fin.elim0 j)) i

#print axioms exact_OpenCoverLambdaBumpPair

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowBumpProof
