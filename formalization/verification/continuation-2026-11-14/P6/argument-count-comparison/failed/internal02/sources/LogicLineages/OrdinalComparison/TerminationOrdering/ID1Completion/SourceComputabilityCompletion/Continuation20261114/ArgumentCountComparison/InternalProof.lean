module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.StepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn suc zRelabel sucRelabel eqnRelabel)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph

theorem internalNil : Targets.InternalNil := by
  intro body alpha Delta left right
  exact InternalRawListRecursionProof.nilValue (constant 2 1) step (numeral 1)
    (Fin.cons left (Fin.cons right Fin.elim0))
    (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 1 (Fin.cons left (Fin.cons right Fin.elim0)))

theorem internalCons : Targets.InternalCons := by
  intro body alpha Delta list head tail left right lc rc hc hl hr
  constructor
  · intro h
    have hw := InternalRawListRecursionProof.consForward (constant 2 1) step list head tail (numeral 1)
      (Fin.cons left (Fin.cons right Fin.elim0)) hc h
    apply InternalRawListRecursionProof.stepCases (constant 2 1) step (numeral 1) head tail
      (Fin.cons left (Fin.cons right Fin.elim0)) _ hw
    intro beta j Theta acc hj ht hs
    simp only [conjunctionRename,eqnRelabel,graph3Rename,numeral,sucRelabel,zRelabel]
    have hl' := renameInto hl j Theta hj
    have hr' := renameInto hr j Theta hj
    rw [graph2Rename] at hl' hr'
    have hparams : (fun i : Fin 2 => (Fin.cons left (Fin.cons right Fin.elim0) i).relabel j) =
        Fin.cons (left.relabel j) (Fin.cons (right.relabel j) Fin.elim0) := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
    rw [hparams] at ht hs
    have hfour : Fin.cons (head.relabel j) (Fin.cons acc
        (Fin.cons (left.relabel j) (Fin.cons (right.relabel j) Fin.elim0))) =
        ![head.relabel j,acc,left.relabel j,right.relabel j] := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) i
    rw [hfour] at hs
    have hv : Nonempty (Derivation body Theta (programGraph step (numeral 1)
        ![head.relabel j,acc,left.relabel j,right.relabel j])) := by
      simpa only [numeral,sucRelabel,zRelabel] using hs
    obtain ⟨he⟩ := StepProof.stepRecover (head.relabel j) acc (left.relabel j) (right.relabel j)
      (lc.relabel j) (rc.relabel j) hl' hr' hv
    have ht' : Nonempty (Derivation body Theta (graph3 allCounts acc (tail.relabel j)
      (left.relabel j) (right.relabel j))) := ht
    have ho := outputTransport allCounts acc (numeral 1)
      ![tail.relabel j,left.relabel j,right.relabel j] ⟨Derivation.conjunctionRight he⟩ ht'
    obtain ⟨ho⟩ := ho
    exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft he) ho⟩
  · rintro ⟨h⟩
    exact InternalRawListRecursionProof.consValue (constant 2 1) step list head tail (numeral 1) (numeral 1)
      (Fin.cons left (Fin.cons right Fin.elim0)) hc ⟨Derivation.conjunctionRight h⟩
      (StepProof.stepIntro head left right lc rc hl hr ⟨Derivation.conjunctionLeft h⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.InternalProof
