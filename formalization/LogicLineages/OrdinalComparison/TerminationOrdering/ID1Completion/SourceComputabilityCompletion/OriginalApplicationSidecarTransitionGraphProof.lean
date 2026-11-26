module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionPipelineDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionGraphProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof (symm refl)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalApplicationSidecarTransitionPipelineDefinitions

theorem binaryIffRename {beta : Type} (p q : Program 2)
    (out input parameter : OrdinaryArithmetic.Term alpha) (j : alpha → beta) :
    ((graph2 p out input parameter).iff (graph2 q out input parameter)).relabel j =
      (graph2 p (out.relabel j) (input.relabel j) (parameter.relabel j)).iff
        (graph2 q (out.relabel j) (input.relabel j) (parameter.relabel j)) := by
  change ((graph2 p out input parameter).relabel j).iff
    ((graph2 q out input parameter).relabel j) = _
  rw [graph2Rename, graph2Rename]

/-- Functionality compares arbitrary outputs to an internally bound common output. -/
theorem commonOutputIff (p q : Program 2)
    (candidate out input parameter : OrdinaryArithmetic.Term alpha)
    (hp : Nonempty (Derivation body Delta (graph2 p candidate input parameter)))
    (hq : Nonempty (Derivation body Delta (graph2 q candidate input parameter))) :
    Nonempty (Derivation body Delta
      ((graph2 p out input parameter).iff (graph2 q out input parameter))) := by
  let xs : Fin 2 → OrdinaryArithmetic.Term alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
  have forward : Nonempty (Derivation body (graph2 p out input parameter :: Delta)
      (graph2 q out input parameter)) := by
    obtain ⟨he⟩ := valueUnique p out candidate xs
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hp _)
    exact outputTransport q candidate out xs ⟨symm he⟩ (withHyp hq _)
  have backward : Nonempty (Derivation body (graph2 q out input parameter :: Delta)
      (graph2 p out input parameter)) := by
    obtain ⟨he⟩ := valueUnique q out candidate xs
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hq _)
    exact outputTransport p candidate out xs ⟨symm he⟩ (withHyp hp _)
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

/-- Exact shared observer values make both actual guards select the previous value. -/
theorem observedValue (active : Program 2) (mark : Program 1) (previous : Program 2)
    (candidate input parameter value : OrdinaryArithmetic.Term alpha)
    (ha : Nonempty (Derivation body Delta (graph2 active (suc z) input parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 previous candidate input parameter)))
    (hc : Nonempty (Derivation body Delta (graph1 mark value candidate)))
    (hi : Nonempty (Derivation body Delta (graph1 mark value input))) :
    Nonempty (Derivation body Delta
      (graph2 (observed active mark previous) candidate input parameter)) := by
  let xs : Fin 2 → OrdinaryArithmetic.Term alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
  have hleft := InternalApplicationCertificateConstructorsSupportProof.unaryValue
    mark previous value candidate xs hc hp
  have hright := InternalApplicationCertificateConstructorsSupportProof.unaryValue
    mark (.projection 0) value input xs hi (projectionValue 0 xs)
  have hm := InternalApplicationStepPeelSupportProof.sameAccept _ _ value xs hleft hright
  have inner := InternalAcceptanceBranchProof.successorBranchIntro _ (.projection 0) previous candidate z xs hm hp
  exact InternalAcceptanceBranchProof.successorBranchIntro active previous _ candidate z xs ha inner

theorem observedZeroValue (active : Program 2) (mark : Program 1) (previous : Program 2)
    (out input parameter : OrdinaryArithmetic.Term alpha)
    (ha : Nonempty (Derivation body Delta (graph2 active z input parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 previous out input parameter))) :
    Nonempty (Derivation body Delta (graph2 (observed active mark previous) out input parameter)) :=
  InternalAcceptanceBranchProof.zeroBranchIntro active previous _ out
    (Fin.cons input (Fin.cons parameter Fin.elim0)) ha hp

theorem observedZeroRecover (active : Program 2) (mark : Program 1) (previous : Program 2)
    (out input parameter : OrdinaryArithmetic.Term alpha)
    (ha : Nonempty (Derivation body Delta (graph2 active z input parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 (observed active mark previous) out input parameter))) :
    Nonempty (Derivation body Delta (graph2 previous out input parameter)) :=
  InternalAcceptanceBranchProof.zeroBranchElim active previous _ out
    (Fin.cons input (Fin.cons parameter Fin.elim0)) ha hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionGraphProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionGraphProof
