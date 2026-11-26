module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureBridgeStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalRunStateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb zRelabel sucRelabel bindEmbedding varBind liftBind)
open OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaTraversalInternalSubstitutionProof
open SourceComputabilityFormulaSupportProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof InternalRecursionClosureSyntaxProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalBoundedDescentNormalizerSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def initialInputs : Fin 4 → Program 2 :=
  ![.projection 0,.projection 1,InternalAcceptance.constantZero 2,InternalAcceptance.constantZero 2]

theorem initialSubstitution : Substitutes initialInputs visitState initial :=
  liveSubstitution (consSubstitution (visitSubstitution (.projection 0) (.projection 1)) (.projection 2)) (.projection 3)

theorem initialAsVisit (state value parameter : OTerm alpha)
    (h : Nonempty (Derivation positive Delta (graph2 initial state value parameter))) :
    Nonempty (Derivation positive Delta (graph4 visitState state value parameter z z)) := by
  apply (substitutionGraph initialSubstitution ![value,parameter,z,z] ![value,parameter] state _).mpr h
  intro i
  exact Fin.cases (projectionValue 0 ![value,parameter]) (Fin.cases (projectionValue 1 ![value,parameter])
    (Fin.cases (InternalLessThanSupportProof.zeroConstantValue ![value,parameter])
      (Fin.cases (InternalLessThanSupportProof.zeroConstantValue ![value,parameter]) (fun k => Fin.elim0 k)))) i

def finishedInputs : Fin 3 → Program 1 :=
  ![.projection 0,InternalAcceptance.constantZero 1,InternalAcceptance.constantZero 1]

theorem finishedSubstitution : Substitutes finishedInputs returnState finishedState :=
  liveSubstitution (.projection 1) (consSubstitution (.projection 0) (.projection 2))

theorem finishedAsReturn (state produced : OTerm alpha)
    (h : Nonempty (Derivation positive Delta (graph1 finishedState state produced))) :
    Nonempty (Derivation positive Delta (graph3 returnState state produced z z)) := by
  apply (substitutionGraph finishedSubstitution ![produced,z,z] ![produced] state _).mpr h
  intro i
  exact Fin.cases (projectionValue 0 ![produced]) (Fin.cases (InternalLessThanSupportProof.zeroConstantValue ![produced])
    (Fin.cases (InternalLessThanSupportProof.zeroConstantValue ![produced]) (fun k => Fin.elim0 k))) i

theorem returnAsFinished (state produced : OTerm alpha)
    (h : Nonempty (Derivation positive Delta (graph3 returnState state produced z z))) :
    Nonempty (Derivation positive Delta (graph1 finishedState state produced)) := by
  apply (substitutionGraph finishedSubstitution ![produced,z,z] ![produced] state _).mp h
  intro i
  exact Fin.cases (projectionValue 0 ![produced]) (Fin.cases (InternalLessThanSupportProof.zeroConstantValue ![produced])
    (Fin.cases (InternalLessThanSupportProof.zeroConstantValue ![produced]) (fun k => Fin.elim0 k))) i

def singletonProgram : Program 1 := consOf (.projection 0) (InternalAcceptance.constantZero 1)

theorem emptySubstitution :
    Substitutes (fun _ : Fin 1 => singletonProgram) emptyState finishedState :=
  liveSubstitution (constantZeroSubstitution _) (.projection 0)

theorem finishedCases (state produced : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation positive Delta (graph1 finishedState state produced)))
    (k : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (singleton : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation positive Theta (graph2 InternalListCodec.consCode singleton (produced.relabel j) z)) →
      Nonempty (Derivation positive Theta (graph1 emptyState (state.relabel j) singleton)) →
      Nonempty (Derivation positive Theta (psi.relabel j))) : Nonempty (Derivation positive Delta psi) := by
  apply programCases InternalListCodec.consCode (Fin.cons produced (Fin.cons z Fin.elim0)) _
  intro beta j Theta singleton hj hc
  simp only [consTermRename,emptyRename,zRelabel] at hc
  have h' := renameInto h j Theta hj
  rw [graph1Rename] at h'
  have hs : Nonempty (Derivation positive Theta (graph1 singletonProgram singleton (produced.relabel j))) :=
    binaryValue InternalListCodec.consCode (.projection 0) (InternalAcceptance.constantZero 1)
      singleton (produced.relabel j) z ![produced.relabel j] hc (projectionValue 0 ![produced.relabel j])
      (InternalLessThanSupportProof.zeroConstantValue ![produced.relabel j])
  have he := (substitutionGraph emptySubstitution ![singleton] ![produced.relabel j]
    (state.relabel j) (by
      intro i
      obtain rfl := Fin.eq_zero i
      exact hs)).mpr h'
  exact k beta j Theta singleton hj hc he

theorem finishedOutput (state produced : OTerm alpha)
    (h : Nonempty (Derivation positive Delta (graph1 finishedState state produced))) :
    Nonempty (Derivation positive Delta (graph1 output produced state)) := by
  apply finishedCases state produced _ h
  intro beta j Theta singleton hj hc he
  rw [graph1Rename]
  exact andRight (InternalApplicationCertifiedResultFoldClosureBridgeStateProof.stateIntro
    (state.relabel j) (produced.relabel j) singleton he hc)

theorem finishedInstantiate (state produced : OTerm alpha) :
    instantiate (graph1 finishedState (state.relabel Sum.inl) (.var (.inr 0))) (emb produced) =
      graph1 finishedState state produced := by
  rw [instantiate,bindEmbedding]
  simp only [graph1,programSubst,consTermSubst,emptySubst,varBind,liftBind]

theorem finishedRunIntro (state produced : OTerm alpha)
    (h : Nonempty (Derivation positive Delta (graph1 finishedState state produced))) :
    Nonempty (Derivation positive Delta (FinishedRun state)) := by
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb produced)
  rw [finishedInstantiate]
  exact h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalRunStateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalRunStateProof
