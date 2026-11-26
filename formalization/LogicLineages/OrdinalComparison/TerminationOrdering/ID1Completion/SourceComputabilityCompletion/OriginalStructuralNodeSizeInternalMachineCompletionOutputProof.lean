module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionIntroductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionOutputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineState
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel)
open InternalTagArithmeticSupportProof (symm)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalStructuralNodeSizeInternalMachineCompletion OriginalStructuralNodeSizeInternalMachineCompletionSyntaxProof
open OriginalStructuralNodeSizeInternalMachineCompletionBindingProof OriginalStructuralNodeSizeInternalMachineCompletionIntroductionProof
open OriginalStructuralNodeSizeInternalMachineCompletionRunProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem producedTransport (d k raw count first second : OTerm alpha)
    (he : Nonempty (Derivation positive Delta (eqn first second)))
    (hc : Nonempty (Derivation positive Delta (Completes d k raw count first))) :
    Nonempty (Derivation positive Delta (Completes d k raw count second)) := by
  apply completesByRuns
  intro beta j Theta work stack start finish hj hi ho
  have he' := renameInto he j Theta hj
  rw [eqnRelabel] at he'
  obtain ⟨he'⟩ := he'
  have hc' := renameInto hc j Theta hj
  rw [completesRename] at hc'
  exact completesApply (d.relabel j) (k.relabel j) (raw.relabel j) (count.relabel j) (first.relabel j)
    work stack start finish hc' hi
    (headTransport returnState finish (second.relabel j) (first.relabel j)
      (Fin.cons work (Fin.cons stack Fin.elim0)) ⟨symm he'⟩ ho)

theorem completionAtFoldCases
    (d k raw produced : OTerm alpha) (psi : Formula alpha)
    (ho : Nonempty (Derivation positive Delta (graph3 (OriginalStructuralNodeSizeInternalMachineCompletion.fold) produced d k raw)))
    (hc : Nonempty (Derivation positive Delta (HasCompletion d k raw raw)))
    (cont : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (count : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation positive Theta
        (InternalPairingSumBounds.weakBound count (payloadFuel (raw.relabel j)))) →
      Nonempty (Derivation positive Theta
        (Completes (d.relabel j) (k.relabel j) (raw.relabel j) count (produced.relabel j))) →
      Nonempty (Derivation positive Theta (psi.relabel j))) : Nonempty (Derivation positive Delta psi) := by
  apply hasCompletionCases d k raw raw psi hc
  intro beta j Theta count actual hj hb hd
  have ho' := renameInto ho j Theta hj
  rw [graph3Rename] at ho'
  have hactual := completionFold (d.relabel j) (k.relabel j) (raw.relabel j) count actual hb hd
  have he := valueUnique (OriginalStructuralNodeSizeInternalMachineCompletion.fold) actual (produced.relabel j)
    (Fin.cons (d.relabel j) (Fin.cons (k.relabel j) (Fin.cons (raw.relabel j) Fin.elim0))) hactual ho'
  exact cont beta j Theta count hj hb
    (producedTransport (d.relabel j) (k.relabel j) (raw.relabel j) count actual (produced.relabel j) he hd)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionOutputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionOutputProof
