module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalOtherTagProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLeafStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaTraversalInternalVisitSyntaxProof
open OriginalLambdaTraversalInternalSubstitutionProof OriginalLambdaTraversalInternalBranchProof
open OriginalLambdaTraversalInternalOtherTagProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def leafInputs (leaf : Program 2) : Fin 3 → Program 1 :=
  ![.composition leaf ![currentRaw,currentParameter],rest,OriginalLambdaTraversal.results]

theorem leafReturnedSubstitution (leaf : Program 2) :
    Substitutes (leafInputs leaf) returnState (leafReturned leaf) :=
  liveSubstitution (.projection 1) (consSubstitution (.projection 0) (.projection 2))

theorem leafForward (leaf : Program 2) (state value parameter suffix stack produced out : OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (graph4 visitState state value parameter suffix stack)))
    (ht : Nonempty (Derivation positive Delta (graph1 otherTag (suc z) value)))
    (hp : Nonempty (Derivation positive Delta (graph2 leaf produced value parameter)))
    (ho : Nonempty (Derivation positive Delta (graph1 (transition leaf) out state))) :
    Nonempty (Derivation positive Delta (graph3 returnState out produced suffix stack)) := by
  apply visitCases state value parameter suffix stack _ hs
  intro beta j Theta codedWork hj hv
  simp only [graph1Rename,graph3Rename]
  have ht' := renameInto ht j Theta hj
  have hp' := renameInto hp j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,sucRelabel,zRelabel] at ht' hp' ho'
  have inputs := openedInputs (state.relabel j) (value.relabel j) (parameter.relabel j)
    (suffix.relabel j) (stack.relabel j) codedWork hv
  have controls := otherControls (state.relabel j) (value.relabel j) (inputs 0) ht'
  have producedAt := binaryValue leaf currentRaw currentParameter (produced.relabel j)
    (value.relabel j) (parameter.relabel j) (Fin.cons (state.relabel j) Fin.elim0) hp' (inputs 0) (inputs 1)
  have li : ∀ i, Nonempty (Derivation positive Theta (programGraph (leafInputs leaf i)
      (![produced.relabel j,suffix.relabel j,stack.relabel j] i) (Fin.cons (state.relabel j) Fin.elim0))) :=
    fun i => Fin.cases producedAt (Fin.cases (inputs 2) (Fin.cases (inputs 3) (fun k => Fin.elim0 k))) i
  exact (substitutionGraph (leafReturnedSubstitution leaf)
    ![produced.relabel j,suffix.relabel j,stack.relabel j]
    (Fin.cons (state.relabel j) Fin.elim0) (out.relabel j) li).mpr
      (leafElim leaf (state.relabel j) (out.relabel j) controls
        (dispatchElim leaf (state.relabel j) (value.relabel j) (parameter.relabel j)
          (suffix.relabel j) (stack.relabel j) codedWork (out.relabel j) hv ho'))

theorem leafBackward (leaf : Program 2) (state value parameter suffix stack produced out : OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (graph4 visitState state value parameter suffix stack)))
    (ht : Nonempty (Derivation positive Delta (graph1 otherTag (suc z) value)))
    (hp : Nonempty (Derivation positive Delta (graph2 leaf produced value parameter)))
    (ho : Nonempty (Derivation positive Delta (graph3 returnState out produced suffix stack))) :
    Nonempty (Derivation positive Delta (graph1 (transition leaf) out state)) := by
  apply visitCases state value parameter suffix stack _ hs
  intro beta j Theta codedWork hj hv
  simp only [graph1Rename,graph3Rename]
  have ht' := renameInto ht j Theta hj
  have hp' := renameInto hp j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,sucRelabel,zRelabel] at ht' hp' ho'
  have inputs := openedInputs (state.relabel j) (value.relabel j) (parameter.relabel j)
    (suffix.relabel j) (stack.relabel j) codedWork hv
  have controls := otherControls (state.relabel j) (value.relabel j) (inputs 0) ht'
  have producedAt := binaryValue leaf currentRaw currentParameter (produced.relabel j)
    (value.relabel j) (parameter.relabel j) (Fin.cons (state.relabel j) Fin.elim0) hp' (inputs 0) (inputs 1)
  have li : ∀ i, Nonempty (Derivation positive Theta (programGraph (leafInputs leaf i)
      (![produced.relabel j,suffix.relabel j,stack.relabel j] i) (Fin.cons (state.relabel j) Fin.elim0))) :=
    fun i => Fin.cases producedAt (Fin.cases (inputs 2) (Fin.cases (inputs 3) (fun k => Fin.elim0 k))) i
  apply dispatchIntro leaf (state.relabel j) (value.relabel j) (parameter.relabel j)
    (suffix.relabel j) (stack.relabel j) codedWork (out.relabel j) hv
  apply leafIntro leaf (state.relabel j) (out.relabel j) controls
  exact (substitutionGraph (leafReturnedSubstitution leaf)
    ![produced.relabel j,suffix.relabel j,stack.relabel j]
    (Fin.cons (state.relabel j) Fin.elim0) (out.relabel j) li).mp ho'

theorem actualOriginalLambdaTraversalInternalLeafStep :
    OriginalLambdaTraversalInternalTargets.ActualOriginalLambdaTraversalInternalLeafStep := by
  intro positive leaf alpha Delta value parameter work results state produced out
  let C := graph4 visitState state value parameter work results ⊓
    (graph1 otherTag (suc z) value ⊓ graph2 leaf produced value parameter)
  let G := graph1 (transition leaf) out state
  let R := graph3 returnState out produced work results
  have hcG : Nonempty (Derivation positive [G,C] C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hcR : Nonempty (Derivation positive [R,C] C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := leafForward leaf state value parameter work results produced out
    (andLeft hcG) (andLeft (andRight hcG)) (andRight (andRight hcG)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := leafBackward leaf state value parameter work results produced out
    (andLeft hcR) (andLeft (andRight hcR)) (andRight (andRight hcR)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨InternalPositiveUnfoldingSupportProof.weakenClosed
    (Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
      (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))) Delta⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLeafStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLeafStepProof
