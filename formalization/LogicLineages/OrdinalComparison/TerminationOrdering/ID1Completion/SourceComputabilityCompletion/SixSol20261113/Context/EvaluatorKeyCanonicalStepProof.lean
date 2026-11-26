module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalTagCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open UniformCertificateCompletion EvaluatorKeyPut EvaluatorKeyCanonicalInductionDefinitions EvaluatorKeyCanonicalSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem atOther (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (left right leftOut rightOut parameter : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (Premises p H G W P left right leftOut rightOut parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one left))) :
 Nonempty (Derivation body Delta (equal leftOut rightOut)) := by
 have dl := andLeft hp
 have dr := andLeft (andRight hp)
 have he := andLeft (andRight (andRight hp))
 have had := EvaluatorKeyOtherDomainProof.admitted p H G W left right parameter dl dr he
 have htr := EvaluatorKeyOtherTransferProof.otherTransfer (baseRepresentative p H G W) H G (member p H G W) W left right parameter had ht
 let leaf := OriginalLambdaTraversalSelection.leaf (refined p H G W P).base (refined p H G W P).window
 obtain ⟨lawl⟩ := OriginalLambdaTraversalInternalLeafProof.actualOriginalLambdaTraversalInternalLeaf body leaf alpha Delta left leftOut parameter
 obtain ⟨lawr⟩ := OriginalLambdaTraversalInternalLeafProof.actualOriginalLambdaTraversalInternalLeaf body leaf alpha Delta right rightOut parameter
 obtain ⟨htl⟩ := ht
 obtain ⟨htr'⟩ := htr
 obtain ⟨cl⟩ := andLeft (andRight (andRight (andRight hp)))
 obtain ⟨cr⟩ := andRight (andRight (andRight (andRight hp)))
 have ll : Nonempty (Derivation body Delta (graph2 leaf leftOut left parameter)) :=
   ⟨Derivation.implicationElimination (Derivation.conjunctionLeft (Derivation.implicationElimination lawl htl)) cl⟩
 have lr : Nonempty (Derivation body Delta (graph2 leaf rightOut right parameter)) :=
   ⟨Derivation.implicationElimination (Derivation.conjunctionLeft (Derivation.implicationElimination lawr htr')) cr⟩
 exact EvaluatorKeyOtherLeafProof.actualOtherLeafEquality p H G W P body alpha Delta left right leftOut rightOut parameter dl dr he ⟨htl⟩ ⟨htr'⟩ ll lr

theorem actualStep : EvaluatorKeyCanonicalInductionTargets.ActualStep := by
 intro p H G W P body alpha Delta q left right leftOut rightOut parameter hb hraw hp
 apply OriginalLambdaTraversalTagCasesProof.tagCases left _
 · intro beta j Theta hj ht
   have hp' := renameInto hp j Theta hj
   rw [premisesRename] at hp'
   rw [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel,← equalEqn]
   have hb' := renameInto hb j Theta hj
   have hraw' := renameInto hraw j Theta hj
   rw [belowPayloadRename] at hb'
   rw [graph1Rename] at hraw'
   exact EvaluatorKeyCanonicalApplicationProof.atTag p H G W P (q.relabel j) (left.relabel j) (right.relabel j)
     (leftOut.relabel j) (rightOut.relabel j) (parameter.relabel j) hb' hraw' hp' ht
 · intro beta j Theta hj ht
   have hp' := renameInto hp j Theta hj
   rw [premisesRename] at hp'
   rw [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel,← equalEqn]
   have hb' := renameInto hb j Theta hj
   have hraw' := renameInto hraw j Theta hj
   rw [belowPayloadRename] at hb'
   rw [graph1Rename] at hraw'
   exact EvaluatorKeyCanonicalLambdaProof.atTag p H G W P (q.relabel j) (left.relabel j) (right.relabel j)
     (leftOut.relabel j) (rightOut.relabel j) (parameter.relabel j) hb' hraw' hp' ht
 · intro beta j Theta hj ht
   have hp' := renameInto hp j Theta hj
   rw [premisesRename] at hp'
   rw [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel,← equalEqn]
   exact atOther p H G W P (left.relabel j) (right.relabel j) (leftOut.relabel j) (rightOut.relabel j) (parameter.relabel j) hp' ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalStepProof
