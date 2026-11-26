module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionRunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineState
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransportInternalMachineCompletionLeafProof OriginalRawSyntaxTransportInternalMachineCompletionRunProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem leafBackward (mode : Mode) (d k value out : OTerm alpha)
    (ht : Nonempty (Derivation positive Delta (graph1 (arityOf (.projection 0)) z value)))
    (ho : Nonempty (Derivation positive Delta (graph3 (leaf mode) out d k value))) :
    Nonempty (Derivation positive Delta (graph3 (fold mode) out d k value)) :=
  completionFold mode d k value (suc z) out (leafBound value)
    (leafComplete mode d k value out ht ho)

theorem leafForward (mode : Mode) (d k value out : OTerm alpha)
    (ht : Nonempty (Derivation positive Delta (graph1 (arityOf (.projection 0)) z value)))
    (ho : Nonempty (Derivation positive Delta (graph3 (fold mode) out d k value))) :
    Nonempty (Derivation positive Delta (graph3 (leaf mode) out d k value)) := by
  apply programCases (leaf mode) (Fin.cons d (Fin.cons k (Fin.cons value Fin.elim0))) _
  intro beta j Theta produced hj hp
  simp only [consTermRename,emptyRename] at hp
  rw [graph3Rename]
  have ht' := renameInto ht j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [graph1Rename,graph3Rename,zRelabel] at ht' ho'
  have hf := leafBackward mode (d.relabel j) (k.relabel j) (value.relabel j) produced ht' hp
  exact outputTransport (leaf mode) produced (out.relabel j)
    ![d.relabel j,k.relabel j,value.relabel j]
    (valueUnique (fold mode) produced (out.relabel j)
      ![d.relabel j,k.relabel j,value.relabel j] hf ho') hp

/-- The original bounded fold is its literal leaf graph at every zero-arity
raw input, including nonzero tag-six payloads and unknown tags. -/
theorem leafRecurrence (mode : Mode) (d k raw out : OTerm alpha) :
    Nonempty (Derivation positive Delta
      ((graph1 (arityOf (.projection 0)) z raw).imp
        ((graph3 (fold mode) out d k raw).iff (graph3 (leaf mode) out d k raw)))) := by
  let C := graph1 (arityOf (.projection 0)) z raw
  let G := graph3 (fold mode) out d k raw
  let R := graph3 (leaf mode) out d k raw
  have hcG : Nonempty (Derivation positive (G :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hcR : Nonempty (Derivation positive (R :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := leafForward mode d k raw out hcG ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := leafBackward mode d k raw out hcR ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafProof
