module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalVisitsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaTraversalInternalVisitSyntaxProof
open OriginalLambdaTraversalInternalSubstitutionProof OriginalLambdaTraversalInternalBranchProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem applicationForward (leaf : Program 2) (state value parameter suffix stack out : OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (graph4 visitState state value parameter suffix stack)))
    (ht : Nonempty (Derivation positive Delta (graph1 rawTag (numeral 2) value)))
    (ho : Nonempty (Derivation positive Delta (graph1 (transition leaf) out state))) :
    Nonempty (Derivation positive Delta (graph4 applicationExpandedState out value parameter suffix stack)) := by
  apply visitCases state value parameter suffix stack _ hs
  intro beta j Theta codedWork hj hv
  simp only [graph1Rename,graph4Rename]
  have ht' := renameInto ht j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [graph1Rename,graph4Rename,SourceComputabilityFormulaSupportProof.numeral,
    sucRelabel,zRelabel] at ht'
  simp only [graph1Rename,graph4Rename] at ho'
  have inputs := openedInputs (state.relabel j) (value.relabel j) (parameter.relabel j)
    (suffix.relabel j) (stack.relabel j) codedWork hv
  have htag : Nonempty (Derivation positive Theta (graph1 currentTag (numeral 2) (state.relabel j))) :=
    unaryValue rawTag currentRaw (numeral 2) (value.relabel j) (Fin.cons (state.relabel j) Fin.elim0)
      ht' (inputs 0)
  exact (substitutionGraph applicationExpandedSubstitution
    ![value.relabel j,parameter.relabel j,suffix.relabel j,stack.relabel j]
    (Fin.cons (state.relabel j) Fin.elim0) (out.relabel j) inputs).mpr
      (applicationElim leaf (state.relabel j) (out.relabel j) htag
        (dispatchElim leaf (state.relabel j) (value.relabel j) (parameter.relabel j)
          (suffix.relabel j) (stack.relabel j) codedWork (out.relabel j) hv ho'))

theorem applicationBackward (leaf : Program 2) (state value parameter suffix stack out : OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (graph4 visitState state value parameter suffix stack)))
    (ht : Nonempty (Derivation positive Delta (graph1 rawTag (numeral 2) value)))
    (ho : Nonempty (Derivation positive Delta (graph4 applicationExpandedState out value parameter suffix stack))) :
    Nonempty (Derivation positive Delta (graph1 (transition leaf) out state)) := by
  apply visitCases state value parameter suffix stack _ hs
  intro beta j Theta codedWork hj hv
  simp only [graph1Rename,graph4Rename]
  have ht' := renameInto ht j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [graph1Rename,graph4Rename,SourceComputabilityFormulaSupportProof.numeral,
    sucRelabel,zRelabel] at ht'
  simp only [graph1Rename,graph4Rename] at ho'
  have inputs := openedInputs (state.relabel j) (value.relabel j) (parameter.relabel j)
    (suffix.relabel j) (stack.relabel j) codedWork hv
  have htag : Nonempty (Derivation positive Theta (graph1 currentTag (numeral 2) (state.relabel j))) :=
    unaryValue rawTag currentRaw (numeral 2) (value.relabel j) (Fin.cons (state.relabel j) Fin.elim0)
      ht' (inputs 0)
  apply dispatchIntro leaf (state.relabel j) (value.relabel j) (parameter.relabel j)
    (suffix.relabel j) (stack.relabel j) codedWork (out.relabel j) hv
  apply applicationIntro leaf (state.relabel j) (out.relabel j) htag
  exact (substitutionGraph applicationExpandedSubstitution
    ![value.relabel j,parameter.relabel j,suffix.relabel j,stack.relabel j]
    (Fin.cons (state.relabel j) Fin.elim0) (out.relabel j) inputs).mp ho'

theorem applicationVisit (leaf : Program 2) (state value parameter suffix stack out : OTerm alpha) :
    Nonempty (Derivation positive Delta
      ((graph4 visitState state value parameter suffix stack ⊓ graph1 rawTag (numeral 2) value).imp
        ((graph1 (transition leaf) out state).iff
          (graph4 applicationExpandedState out value parameter suffix stack)))) := by
  let C := graph4 visitState state value parameter suffix stack ⊓ graph1 rawTag (numeral 2) value
  let G := graph1 (transition leaf) out state
  let R := graph4 applicationExpandedState out value parameter suffix stack
  have hcG : Nonempty (Derivation positive [G,C] C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hcR : Nonempty (Derivation positive [R,C] C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := applicationForward leaf state value parameter suffix stack out
    (andLeft hcG) (andRight hcG) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := applicationBackward leaf state value parameter suffix stack out
    (andLeft hcR) (andRight hcR) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨InternalPositiveUnfoldingSupportProof.weakenClosed
    (Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
      (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))) Delta⟩

theorem lambdaForward (leaf : Program 2) (state value parameter suffix stack out : OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (graph4 visitState state value parameter suffix stack)))
    (ht : Nonempty (Derivation positive Delta (graph1 rawTag (numeral 1) value)))
    (ho : Nonempty (Derivation positive Delta (graph1 (transition leaf) out state))) :
    Nonempty (Derivation positive Delta (graph4 lambdaExpandedState out value parameter suffix stack)) := by
  apply visitCases state value parameter suffix stack _ hs
  intro beta j Theta codedWork hj hv
  simp only [graph1Rename,graph4Rename]
  have ht' := renameInto ht j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [graph1Rename,graph4Rename,SourceComputabilityFormulaSupportProof.numeral,
    sucRelabel,zRelabel] at ht'
  simp only [graph1Rename,graph4Rename] at ho'
  have inputs := openedInputs (state.relabel j) (value.relabel j) (parameter.relabel j)
    (suffix.relabel j) (stack.relabel j) codedWork hv
  have htag : Nonempty (Derivation positive Theta (graph1 currentTag (numeral 1) (state.relabel j))) :=
    unaryValue rawTag currentRaw (numeral 1) (value.relabel j) (Fin.cons (state.relabel j) Fin.elim0)
      ht' (inputs 0)
  exact (substitutionGraph lambdaExpandedSubstitution
    ![value.relabel j,parameter.relabel j,suffix.relabel j,stack.relabel j]
    (Fin.cons (state.relabel j) Fin.elim0) (out.relabel j) inputs).mpr
      (lambdaElim leaf (state.relabel j) (out.relabel j) htag
        (dispatchElim leaf (state.relabel j) (value.relabel j) (parameter.relabel j)
          (suffix.relabel j) (stack.relabel j) codedWork (out.relabel j) hv ho'))

theorem lambdaBackward (leaf : Program 2) (state value parameter suffix stack out : OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (graph4 visitState state value parameter suffix stack)))
    (ht : Nonempty (Derivation positive Delta (graph1 rawTag (numeral 1) value)))
    (ho : Nonempty (Derivation positive Delta (graph4 lambdaExpandedState out value parameter suffix stack))) :
    Nonempty (Derivation positive Delta (graph1 (transition leaf) out state)) := by
  apply visitCases state value parameter suffix stack _ hs
  intro beta j Theta codedWork hj hv
  simp only [graph1Rename,graph4Rename]
  have ht' := renameInto ht j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [graph1Rename,graph4Rename,SourceComputabilityFormulaSupportProof.numeral,
    sucRelabel,zRelabel] at ht'
  simp only [graph1Rename,graph4Rename] at ho'
  have inputs := openedInputs (state.relabel j) (value.relabel j) (parameter.relabel j)
    (suffix.relabel j) (stack.relabel j) codedWork hv
  have htag : Nonempty (Derivation positive Theta (graph1 currentTag (numeral 1) (state.relabel j))) :=
    unaryValue rawTag currentRaw (numeral 1) (value.relabel j) (Fin.cons (state.relabel j) Fin.elim0)
      ht' (inputs 0)
  apply dispatchIntro leaf (state.relabel j) (value.relabel j) (parameter.relabel j)
    (suffix.relabel j) (stack.relabel j) codedWork (out.relabel j) hv
  apply lambdaIntro leaf (state.relabel j) (out.relabel j) htag
  exact (substitutionGraph lambdaExpandedSubstitution
    ![value.relabel j,parameter.relabel j,suffix.relabel j,stack.relabel j]
    (Fin.cons (state.relabel j) Fin.elim0) (out.relabel j) inputs).mp ho'

theorem lambdaVisit (leaf : Program 2) (state value parameter suffix stack out : OTerm alpha) :
    Nonempty (Derivation positive Delta
      ((graph4 visitState state value parameter suffix stack ⊓ graph1 rawTag (numeral 1) value).imp
        ((graph1 (transition leaf) out state).iff
          (graph4 lambdaExpandedState out value parameter suffix stack)))) := by
  let C := graph4 visitState state value parameter suffix stack ⊓ graph1 rawTag (numeral 1) value
  let G := graph1 (transition leaf) out state
  let R := graph4 lambdaExpandedState out value parameter suffix stack
  have hcG : Nonempty (Derivation positive [G,C] C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hcR : Nonempty (Derivation positive [R,C] C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := lambdaForward leaf state value parameter suffix stack out
    (andLeft hcG) (andRight hcG) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := lambdaBackward leaf state value parameter suffix stack out
    (andLeft hcR) (andRight hcR) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨InternalPositiveUnfoldingSupportProof.weakenClosed
    (Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
      (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))) Delta⟩

theorem actualOriginalLambdaTraversalInternalVisits :
    OriginalLambdaTraversalInternalTargets.ActualOriginalLambdaTraversalInternalVisits := by
  intro positive leaf alpha Delta value parameter work results state out
  exact ⟨applicationVisit leaf state value parameter work results out,
    lambdaVisit leaf state value parameter work results out⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalVisitsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalVisitsProof
