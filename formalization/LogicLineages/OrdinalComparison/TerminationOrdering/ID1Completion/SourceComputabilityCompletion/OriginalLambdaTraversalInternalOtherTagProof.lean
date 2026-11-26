module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalOtherTagProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaTraversalInternalBranchProof
open OriginalHereditaryValidityInternalNodeSupportProof (equalityCases weakenProof)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def OtherControls (state : OTerm alpha) : Formula alpha :=
  graph1 (InternalApplicationStepPeel.same currentTag (two 1)) z state ⊓
    graph1 (OriginalHereditaryValidity.exactOne currentTag) z state

@[simp] theorem otherControlsRename {beta : Type} (state : OTerm alpha) (j : alpha → beta) :
    (OtherControls state).relabel j = OtherControls (state.relabel j) := by
  simp only [OtherControls,conjunctionRename,graph1Rename,zRelabel]

theorem constantZeroOneFalse {n : Nat} (xs : Fin n → OTerm alpha)
    (h : Nonempty (Derivation positive Delta (programGraph (InternalAcceptance.constantZero n) (suc z) xs))) :
    Nonempty (Derivation positive Delta (⊥ : Formula alpha)) := by
  obtain ⟨he⟩ := valueUnique (InternalAcceptance.constantZero n) (suc z) z xs h
    (InternalLessThanSupportProof.zeroConstantValue xs)
  exact ⟨sucNeZeroApply he⟩

theorem otherControls (state value : OTerm alpha)
    (hr : Nonempty (Derivation positive Delta (graph1 currentRaw value state)))
    (ho : Nonempty (Derivation positive Delta (graph1 otherTag (suc z) value))) :
    Nonempty (Derivation positive Delta (OtherControls state)) := by
  apply programCases rawTag (Fin.cons value Fin.elim0) _
  intro beta j Theta tag hj ht
  simp only [consTermRename,emptyRename] at ht
  rw [otherControlsRename]
  have hr' := renameInto hr j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hr' ho'
  let vs : Fin 1 → OTerm beta := Fin.cons (value.relabel j) Fin.elim0
  let ss : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  have hc : Nonempty (Derivation positive Theta (graph1 currentTag tag (state.relabel j))) :=
    unaryValue rawTag currentRaw tag (value.relabel j) ss ht hr'
  apply equalityCases tag (numeral 2) _
  · intro Xi inc h2
    have hraw2 := binaryValue InternalEqualityTest.equalityTest rawTag (two 1) z tag (numeral 2) vs
      h2 (weakenProof ht inc) (twoValue vs)
    have hstate2 := binaryValue InternalEqualityTest.equalityTest currentTag (two 1) z tag (numeral 2) ss
      h2 (weakenProof hc inc) (twoValue ss)
    have hinner := zeroBranchElim _ _ _ (suc z) vs hraw2 (weakenProof ho' inc)
    apply equalityCases tag (suc z) _
    · intro Omega inc2 h1
      have hstate1 := binaryValue InternalEqualityTest.equalityTest currentTag (InternalLessThan.constantOne 1)
        z tag (suc z) ss h1 (weakenProof hc (fun p hp => inc2 p (inc p hp)))
        (InternalLessThanSupportProof.oneConstantValue ss)
      exact andIntro (weakenProof hstate2 inc2) hstate1
    · intro Omega inc2 h1
      have hraw1 := binaryValue InternalEqualityTest.equalityTest rawTag (InternalLessThan.constantOne 1)
        (suc z) tag (suc z) vs h1 (weakenProof ht (fun p hp => inc2 p (inc p hp)))
        (InternalLessThanSupportProof.oneConstantValue vs)
      obtain ⟨hf⟩ := constantZeroOneFalse vs
        (successorBranchElim _ _ _ (suc z) z vs hraw1 (weakenProof hinner inc2))
      exact ⟨Derivation.explosion hf⟩
  · intro Xi inc h2
    have hraw2 := binaryValue InternalEqualityTest.equalityTest rawTag (two 1) (suc z) tag (numeral 2) vs
      h2 (weakenProof ht inc) (twoValue vs)
    obtain ⟨hf⟩ := constantZeroOneFalse vs
      (successorBranchElim _ _ _ (suc z) z vs hraw2 (weakenProof ho' inc))
    exact ⟨Derivation.explosion hf⟩

theorem leafIntro (leaf : Program 2) (state out : OTerm alpha)
    (hc : Nonempty (Derivation positive Delta (OtherControls state)))
    (ho : Nonempty (Derivation positive Delta (graph1 (leafReturned leaf) out state))) :
    Nonempty (Derivation positive Delta (graph1 (visitDispatch leaf) out state)) :=
  zeroBranchIntro _ _ _ out (Fin.cons state Fin.elim0) (andLeft hc)
    (zeroBranchIntro _ _ _ out (Fin.cons state Fin.elim0) (andRight hc) ho)

theorem leafElim (leaf : Program 2) (state out : OTerm alpha)
    (hc : Nonempty (Derivation positive Delta (OtherControls state)))
    (ho : Nonempty (Derivation positive Delta (graph1 (visitDispatch leaf) out state))) :
    Nonempty (Derivation positive Delta (graph1 (leafReturned leaf) out state)) :=
  zeroBranchElim _ _ _ out (Fin.cons state Fin.elim0) (andRight hc)
    (zeroBranchElim _ _ _ out (Fin.cons state Fin.elim0) (andLeft hc) ho)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalOtherTagProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalOtherTagProof
