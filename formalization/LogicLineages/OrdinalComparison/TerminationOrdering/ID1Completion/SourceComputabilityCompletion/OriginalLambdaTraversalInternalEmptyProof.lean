module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackInternalSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalEmptyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalGraphCompositionFunctionalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Empty work is selected internally from the original nested pair graph. -/
theorem emptyFixed (leaf : Program 2)
    (results state : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 emptyState state results))) :
    Nonempty (Derivation body Gamma (graph1 (transition leaf) state state)) := by
  apply programCases InternalPairing.pairing (Fin.cons z (Fin.cons results Fin.elim0)) _
  intro β j Delta packed hj hp
  simp only [graph1Rename]
  simp only [consTermRename,emptyRename,zRelabel] at hp
  have hs' := renameInto hs j Delta hj
  simp only [graph1Rename] at hs'
  let xs : Fin 1 → OTerm β := Fin.cons (results.relabel j) Fin.elim0
  let ss : Fin 1 → OTerm β := Fin.cons (state.relabel j) Fin.elim0
  have hi := binaryValue InternalPairing.pairing (InternalAcceptance.constantZero 1)
    (.projection 0) packed z (results.relabel j) xs hp
    (InternalLessThanSupportProof.zeroConstantValue xs) (projectionValue 0 xs)
  have ho := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 1)
    (pairOf (InternalAcceptance.constantZero 1) (.projection 0))
    (state.relabel j) (suc z) packed xs hs'
    (InternalLessThanSupportProof.oneConstantValue xs) hi
  have hstatus := pairLeft (state.relabel j) (suc z) packed ho
  have hwork := unaryValue InternalUnpair.left InternalUnpair.right z packed ss
    (pairLeft packed z (results.relabel j) hp)
    (pairRight (state.relabel j) (suc z) packed ho)
  have haccept := sameAccept status (InternalLessThan.constantOne 1) (suc z) ss hstatus
    (InternalLessThanSupportProof.oneConstantValue ss)
  apply successorBranchIntro _ _ _ (state.relabel j) z ss haccept
  exact zeroBranchIntro _ _ _ (state.relabel j) ss hwork (projectionValue 0 ss)

theorem actualOriginalLambdaTraversalInternalEmpty :
    OriginalLambdaTraversalInternalTargets.ActualOriginalLambdaTraversalInternalEmpty := by
  intro body leaf α Delta results state out
  let c := graph1 emptyState state results
  let g := graph1 (transition leaf) out state
  let r := equal out state
  have hc₁ : Nonempty (Derivation body (g :: c :: Delta) c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hc₂ : Nonempty (Derivation body (r :: c :: Delta) c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := valueUnique (transition leaf) out state
    (Fin.cons state Fin.elim0) ⟨Derivation.hypothesis List.mem_cons_self⟩
    (emptyFixed leaf results state hc₁)
  have heq : Nonempty (Derivation body (r :: c :: Delta) (InternalTagArithmeticSyntaxProof.eqn state out)) := by
    have hr : Derivation body (r :: c :: Delta) r := Derivation.hypothesis List.mem_cons_self
    have hr' : Derivation body (r :: c :: Delta) (InternalTagArithmeticSyntaxProof.eqn out state) := by
      simpa only [r,equalEqn] using hr
    exact ⟨InternalTagArithmeticSupportProof.symm hr'⟩
  obtain ⟨hb⟩ := outputTransport (transition leaf) state out
    (Fin.cons state Fin.elim0) heq (emptyFixed leaf results state hc₂)
  have hf' : Derivation body (g :: c :: Delta) r := by simpa only [r,equalEqn] using hf
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf') (Derivation.implicationIntroduction hb))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalEmptyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalEmptyProof
