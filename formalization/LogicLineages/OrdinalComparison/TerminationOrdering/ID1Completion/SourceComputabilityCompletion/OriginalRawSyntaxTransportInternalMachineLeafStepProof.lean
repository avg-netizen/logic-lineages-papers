module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineLeafStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineState
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalLambdaConstructorGraphSyntaxProof OriginalRawSyntaxTransportInternalMachineVisitProof
open OriginalLambdaTraversalInternalSubstitutionProof OriginalRawSyntaxTransportInternalMachineBranchProof
open OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def leafInputs (mode : Mode) : Fin 3 → Program 1 :=
  ![.composition (leaf mode) ![currentType,currentCutoff,currentRaw],rest,OriginalRawSyntaxTransport.results]

theorem leafReturnedSubstitution (mode : Mode) :
    Substitutes (leafInputs mode) returnState (leafReturned mode) :=
  liveSubstitution (.projection 1) (consSubstitution (.projection 0) (.projection 2))

theorem leafForward (mode : Mode) (state d k value suffix stack produced out : OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (graph5 visitState state d k value suffix stack)))
    (ht : Nonempty (Derivation positive Delta (graph1 (arityOf (.projection 0)) z value)))
    (hp : Nonempty (Derivation positive Delta (graph3 (leaf mode) produced d k value)))
    (ho : Nonempty (Derivation positive Delta (graph1 (transition mode) out state))) :
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
  have producedAt := compositionValue (leaf mode) ![currentType,currentCutoff,currentRaw]
    (produced.relabel j) (Fin.cons (state.relabel j) Fin.elim0)
    ![d.relabel j,k.relabel j,value.relabel j] hp'
    (fun i => Fin.cases (inputs 0) (Fin.cases (inputs 1) (Fin.cases (inputs 2) (fun a => Fin.elim0 a))) i)
  have li : ∀ i, Nonempty (Derivation positive Theta (programGraph (leafInputs mode i)
      (![produced.relabel j,suffix.relabel j,stack.relabel j] i) (Fin.cons (state.relabel j) Fin.elim0))) :=
    fun i => Fin.cases producedAt (Fin.cases (inputs 3) (Fin.cases (inputs 4) (fun k => Fin.elim0 k))) i
  exact (substitutionGraph (leafReturnedSubstitution mode)
    ![produced.relabel j,suffix.relabel j,stack.relabel j]
    (Fin.cons (state.relabel j) Fin.elim0) (out.relabel j) li).mpr
      (leafElim mode (state.relabel j) (out.relabel j) controls
        (dispatchElim mode (state.relabel j) (d.relabel j) (k.relabel j) (value.relabel j)
          (suffix.relabel j) (stack.relabel j) codedWork (out.relabel j) hv ho'))

theorem leafBackward (mode : Mode) (state d k value suffix stack produced out : OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (graph5 visitState state d k value suffix stack)))
    (ht : Nonempty (Derivation positive Delta (graph1 (arityOf (.projection 0)) z value)))
    (hp : Nonempty (Derivation positive Delta (graph3 (leaf mode) produced d k value)))
    (ho : Nonempty (Derivation positive Delta (graph3 returnState out produced suffix stack))) :
    Nonempty (Derivation positive Delta (graph1 (transition mode) out state)) := by
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
  have producedAt := compositionValue (leaf mode) ![currentType,currentCutoff,currentRaw]
    (produced.relabel j) (Fin.cons (state.relabel j) Fin.elim0)
    ![d.relabel j,k.relabel j,value.relabel j] hp'
    (fun i => Fin.cases (inputs 0) (Fin.cases (inputs 1) (Fin.cases (inputs 2) (fun a => Fin.elim0 a))) i)
  have li : ∀ i, Nonempty (Derivation positive Theta (programGraph (leafInputs mode i)
      (![produced.relabel j,suffix.relabel j,stack.relabel j] i) (Fin.cons (state.relabel j) Fin.elim0))) :=
    fun i => Fin.cases producedAt (Fin.cases (inputs 3) (Fin.cases (inputs 4) (fun k => Fin.elim0 k))) i
  apply dispatchIntro mode (state.relabel j) (d.relabel j) (k.relabel j) (value.relabel j)
    (suffix.relabel j) (stack.relabel j) codedWork (out.relabel j) hv
  apply leafIntro mode (state.relabel j) (out.relabel j) controls
  exact (substitutionGraph (leafReturnedSubstitution mode)
    ![produced.relabel j,suffix.relabel j,stack.relabel j]
    (Fin.cons (state.relabel j) Fin.elim0) (out.relabel j) li).mp ho'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineLeafStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineLeafStepProof
