module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaCellQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsWrapperCongruenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaAgreementProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (queryCases andIntro andLeft andRight)
open InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof (fieldsRename)
open OriginalLambdaTraversalInternalFieldsSyntaxProof (lambdaFieldsRename)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem cells (Q : Program 2) (input other domain codomain child otherChild parameter childParameter c gamma extended count childRow otherChildRow tail otherTail : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields input domain codomain child parameter childParameter)))
 (hf2 : Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields other domain codomain otherChild parameter childParameter)))
 (hc : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor input domain codomain child)))
 (hc2 : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor other domain codomain otherChild)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hlen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count gamma)))
 (hext : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended domain gamma)))
 (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter c extended)))
 (hr : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows Q) childRow child childParameter)))
 (hr2 : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows Q) otherChildRow otherChild childParameter)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.drop tail (numeral 1) childRow)))
 (ht2 : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.drop otherTail (numeral 1) otherChildRow)))
 (heq : Nonempty (Derivation body Delta (equal tail otherTail)))
 :
 Nonempty (Derivation body Delta (OriginalHereditaryDeletionRowsCongruence.CellAgreement (OriginalRootObservation.rootObservation Q) count input parameter other parameter)) := by
 unfold OriginalHereditaryDeletionRowsCongruence.CellAgreement
 apply InternalClosedProgramsBindingProof.actualFiniteUniversalIntroduction body alpha 3 Delta
 let rho : alpha → alpha ⊕ Fin 3 := Sum.inl
 let cutoff : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
 let out : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
 let otherOut : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
 let A := OriginalHereditaryDeletionRowsCongruence.cellFields (OriginalRootObservation.rootObservation Q) (count.relabel rho) (input.relabel rho) (parameter.relabel rho) (other.relabel rho) (parameter.relabel rho) cutoff out otherOut
 let Theta := A :: Delta.map (fun f => f.relabel rho)
 have h : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hrho : ∀ f ∈ Delta, f.relabel rho ∈ Theta := fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
 have hf' := renameInto hf rho Theta hrho
 simp only [lambdaFieldsRename] at hf'
 have hf2' := renameInto hf2 rho Theta hrho
 simp only [lambdaFieldsRename] at hf2'
 have hc' := renameInto hc rho Theta hrho
 simp only [graph3Rename] at hc'
 have hc2' := renameInto hc2 rho Theta hrho
 simp only [graph3Rename] at hc2'
 have hp' := renameInto hp rho Theta hrho
 simp only [graph2Rename] at hp'
 have hlen' := renameInto hlen rho Theta hrho
 simp only [OriginalContextInsertionSyntaxProof.lengthRename] at hlen'
 have hext' := renameInto hext rho Theta hrho
 simp only [graph2Rename] at hext'
 have hcp' := renameInto hcp rho Theta hrho
 simp only [graph2Rename] at hcp'
 have hr' := renameInto hr rho Theta hrho
 simp only [graph2Rename] at hr'
 have hr2' := renameInto hr2 rho Theta hrho
 simp only [graph2Rename] at hr2'
 have ht' := renameInto ht rho Theta hrho
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at ht'
 have ht2' := renameInto ht2 rho Theta hrho
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at ht2'
 have heq' := renameInto heq rho Theta hrho
 simp only [OriginalTypedDecoderInternalLogicSyntaxProof.equalRename] at heq'
 obtain ⟨hc⟩ := OriginalHereditaryDeletionRowsLambdaCellQueryProof.cell Q (input.relabel rho) (other.relabel rho) (domain.relabel rho) (codomain.relabel rho) (child.relabel rho) (otherChild.relabel rho) (parameter.relabel rho) (childParameter.relabel rho) (c.relabel rho) (gamma.relabel rho) (extended.relabel rho) (count.relabel rho) (childRow.relabel rho) (otherChildRow.relabel rho) (tail.relabel rho) (otherTail.relabel rho) cutoff out otherOut
  hf' hf2' hc' hc2' hp' hlen' hext' hcp' hr' hr2' ht' ht2' heq' (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
 simpa only [OriginalHereditaryDeletionRowsCongruence.cellBody,rho] using (Nonempty.intro (Derivation.implicationIntroduction hc))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaAgreementProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaAgreementProof
