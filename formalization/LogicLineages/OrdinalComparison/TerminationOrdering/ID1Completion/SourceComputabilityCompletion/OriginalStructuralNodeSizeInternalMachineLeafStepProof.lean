module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineLeafStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineState
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalLambdaConstructorGraphSyntaxProof OriginalRawSyntaxTransportInternalMachineVisitProof
open OriginalLambdaTraversalInternalSubstitutionProof OriginalStructuralNodeSizeInternalMachineBranchProof
open OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open InternalTagArithmeticSupportProof (symm)
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def leafInputs : Fin 3 → Program 1 :=
  ![constant 1 1,rest,OriginalRawSyntaxTransport.results]

theorem leafReturnedSubstitution :
    Substitutes (leafInputs) returnState (OriginalStructuralNodeSize.leafReturned) :=
  liveSubstitution (.projection 1) (consSubstitution (.projection 0) (.projection 2))

theorem leafForward (state d k value suffix stack produced out : OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (graph5 visitState state d k value suffix stack)))
    (ht : Nonempty (Derivation positive Delta (graph1 (arityOf (.projection 0)) z value)))
    (hp : Nonempty (Derivation positive Delta (graph3 (constant 3 1) produced d k value)))
    (ho : Nonempty (Derivation positive Delta (graph1 (OriginalStructuralNodeSize.transition) out state))) :
    Nonempty (Derivation positive Delta (graph3 returnState out produced suffix stack)) := by
  apply visitCases state d k value suffix stack _ hs
  intro beta j Theta codedWork hj hv
  simp only [graph1Rename,graph3Rename]
  have ht' := renameInto ht j Theta hj
  have hp' := renameInto hp j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,sucRelabel,zRelabel] at ht' hp' ho'
  have inputs := openedInputs (state.relabel j) (d.relabel j) (k.relabel j) (value.relabel j)
    (suffix.relabel j) (stack.relabel j) codedWork hv
  have controls := arityValueAt currentRaw z (value.relabel j)
    (Fin.cons (state.relabel j) Fin.elim0) (inputs 2) ht'
  have he := valueUnique (constant 3 1) (produced.relabel j) (suc z)
    ![d.relabel j,k.relabel j,value.relabel j] hp'
    (constantValue 1 ![d.relabel j,k.relabel j,value.relabel j])
  obtain ⟨he⟩ := he
  have producedAt := outputTransport (constant 1 1) (suc z) (produced.relabel j)
    (Fin.cons (state.relabel j) Fin.elim0) ⟨symm he⟩
    (constantValue 1 (Fin.cons (state.relabel j) Fin.elim0))
  have li : ∀ i, Nonempty (Derivation positive Theta (programGraph (leafInputs i)
      (![produced.relabel j,suffix.relabel j,stack.relabel j] i) (Fin.cons (state.relabel j) Fin.elim0))) :=
    fun i => Fin.cases producedAt (Fin.cases (inputs 3) (Fin.cases (inputs 4) (fun k => Fin.elim0 k))) i
  exact (substitutionGraph (leafReturnedSubstitution)
    ![produced.relabel j,suffix.relabel j,stack.relabel j]
    (Fin.cons (state.relabel j) Fin.elim0) (out.relabel j) li).mpr
      (leafElim (state.relabel j) (out.relabel j) controls
        (dispatchElim (state.relabel j) (d.relabel j) (k.relabel j) (value.relabel j)
          (suffix.relabel j) (stack.relabel j) codedWork (out.relabel j) hv ho'))

theorem leafBackward (state d k value suffix stack produced out : OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (graph5 visitState state d k value suffix stack)))
    (ht : Nonempty (Derivation positive Delta (graph1 (arityOf (.projection 0)) z value)))
    (hp : Nonempty (Derivation positive Delta (graph3 (constant 3 1) produced d k value)))
    (ho : Nonempty (Derivation positive Delta (graph3 returnState out produced suffix stack))) :
    Nonempty (Derivation positive Delta (graph1 (OriginalStructuralNodeSize.transition) out state)) := by
  apply visitCases state d k value suffix stack _ hs
  intro beta j Theta codedWork hj hv
  simp only [graph1Rename,graph3Rename]
  have ht' := renameInto ht j Theta hj
  have hp' := renameInto hp j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,sucRelabel,zRelabel] at ht' hp' ho'
  have inputs := openedInputs (state.relabel j) (d.relabel j) (k.relabel j) (value.relabel j)
    (suffix.relabel j) (stack.relabel j) codedWork hv
  have controls := arityValueAt currentRaw z (value.relabel j)
    (Fin.cons (state.relabel j) Fin.elim0) (inputs 2) ht'
  have he := valueUnique (constant 3 1) (produced.relabel j) (suc z)
    ![d.relabel j,k.relabel j,value.relabel j] hp'
    (constantValue 1 ![d.relabel j,k.relabel j,value.relabel j])
  obtain ⟨he⟩ := he
  have producedAt := outputTransport (constant 1 1) (suc z) (produced.relabel j)
    (Fin.cons (state.relabel j) Fin.elim0) ⟨symm he⟩
    (constantValue 1 (Fin.cons (state.relabel j) Fin.elim0))
  have li : ∀ i, Nonempty (Derivation positive Theta (programGraph (leafInputs i)
      (![produced.relabel j,suffix.relabel j,stack.relabel j] i) (Fin.cons (state.relabel j) Fin.elim0))) :=
    fun i => Fin.cases producedAt (Fin.cases (inputs 3) (Fin.cases (inputs 4) (fun k => Fin.elim0 k))) i
  apply dispatchIntro (state.relabel j) (d.relabel j) (k.relabel j) (value.relabel j)
    (suffix.relabel j) (stack.relabel j) codedWork (out.relabel j) hv
  apply leafIntro (state.relabel j) (out.relabel j) controls
  exact (substitutionGraph (leafReturnedSubstitution)
    ![produced.relabel j,suffix.relabel j,stack.relabel j]
    (Fin.cons (state.relabel j) Fin.elim0) (out.relabel j) li).mp ho'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineLeafStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineLeafStepProof
