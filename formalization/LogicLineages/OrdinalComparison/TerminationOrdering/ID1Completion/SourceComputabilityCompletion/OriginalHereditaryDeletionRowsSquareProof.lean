module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (queryCases andIntro andLeft andRight)
open InternalRecursionGraphStepSyntaxProof
open InternalOriginalUniformVertexPathSupportProof (ternaryRecover)
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open OriginalClassContextAllPositionObserver
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem square (Q : Program 2) (gamma count i j c parameter input upper upperParameter lower lowerParameter upperRow lowerRow upperValue lowerValue : OTerm alpha)
 (hlen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (suc count) gamma)))
 (hi : Nonempty (Derivation body Delta (OriginalContextInsertion.Below i (suc j))))
 (hj : Nonempty (Derivation body Delta (OriginalContextInsertion.Below (suc j) (suc count))))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (heU : Nonempty (Derivation body Delta (graph3 erasedPacked upper (suc j) input parameter)))
 (hpU : Nonempty (Derivation body Delta (graph3 erasedParameter upperParameter (suc j) input parameter)))
 (heL : Nonempty (Derivation body Delta (graph3 erasedPacked lower i input parameter)))
 (hpL : Nonempty (Derivation body Delta (graph3 erasedParameter lowerParameter i input parameter)))
 (hrU : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows Q) upperRow upper upperParameter)))
 (hrL : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows Q) lowerRow lower lowerParameter)))
 (hvU : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup upperValue i upperRow)))
 (hvL : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup lowerValue j lowerRow)))
 :
 Nonempty (Derivation body Delta (equal upperValue lowerValue ⊓ (OriginalContextInsertion.lengthGraph count upperRow ⊓ OriginalContextInsertion.lengthGraph count lowerRow))) := by
 apply OriginalHereditaryDeletionRowsSquareQueryProof.coordinateCases gamma i j upper lower c _
 intro beta rho Theta a b u l ul lu xl xr pl pr hrho ha hb hu hl hul hlu hxl hxr hpl hpr
 simp only [InternalRecursionGraphStepSyntaxProof.conjunctionRename,OriginalTypedDecoderInternalLogicSyntaxProof.equalRename,OriginalContextInsertionSyntaxProof.lengthRename]
 have hlen' := renameInto hlen rho Theta hrho
 simp only [OriginalContextInsertionSyntaxProof.lengthRename,sucRelabel] at hlen'
 have hi' := renameInto hi rho Theta hrho
 simp only [OriginalContextInsertion.Below,InternalOriginalOrderSyntaxProof.orderRename,sucRelabel] at hi'
 have hj' := renameInto hj rho Theta hrho
 simp only [OriginalContextInsertion.Below,InternalOriginalOrderSyntaxProof.orderRename,sucRelabel] at hj'
 have hp' := renameInto hp rho Theta hrho
 simp only [graph2Rename] at hp'
 have heU' := renameInto heU rho Theta hrho
 simp only [graph3Rename,sucRelabel] at heU'
 have hpU' := renameInto hpU rho Theta hrho
 simp only [graph3Rename,sucRelabel] at hpU'
 have heL' := renameInto heL rho Theta hrho
 simp only [graph3Rename,sucRelabel] at heL'
 have hpL' := renameInto hpL rho Theta hrho
 simp only [graph3Rename,sucRelabel] at hpL'
 have hrU' := renameInto hrU rho Theta hrho
 simp only [graph2Rename] at hrU'
 have hrL' := renameInto hrL rho Theta hrho
 simp only [graph2Rename] at hrL'
 have hvU' := renameInto hvU rho Theta hrho
 simp only [graph2Rename] at hvU'
 have hvL' := renameInto hvL rho Theta hrho
 simp only [graph2Rename] at hvL'
 exact OriginalHereditaryDeletionRowsSquareCoreProof.atCoordinates Q (gamma.relabel rho) (count.relabel rho) (i.relabel rho) (j.relabel rho) (c.relabel rho) (parameter.relabel rho) (input.relabel rho) (upper.relabel rho) (upperParameter.relabel rho) (lower.relabel rho) (lowerParameter.relabel rho) (upperRow.relabel rho) (lowerRow.relabel rho) (upperValue.relabel rho) (lowerValue.relabel rho) a b u l ul lu xl xr pl pr
  hlen' hi' hj' hp' heU' hpU' heL' hpL' hrU' hrL' hvU' hvL' ha hb hu hl hul hlu hxl hxr hpl hpr

theorem actualIndexedRowSquare : OriginalHereditaryDeletionRowsSquareTargets.ActualIndexedRowSquare := by
 intro Q body alpha Delta gamma count i j c parameter input upper upperParameter lower lowerParameter upperRow lowerRow upperValue lowerValue
 let A : Formula alpha := OriginalContextInsertion.lengthGraph (suc count) gamma ⊓ (OriginalContextInsertion.Below i (suc j) ⊓ (OriginalContextInsertion.Below (suc j) (suc count) ⊓ (graph2 InternalPairing.pairing parameter c gamma ⊓ (graph3 erasedPacked upper (suc j) input parameter ⊓ (graph3 erasedParameter upperParameter (suc j) input parameter ⊓ (graph3 erasedPacked lower i input parameter ⊓ (graph3 erasedParameter lowerParameter i input parameter ⊓ (graph2 (OriginalHereditaryDeletionRows.rows Q) upperRow upper upperParameter ⊓ (graph2 (OriginalHereditaryDeletionRows.rows Q) lowerRow lower lowerParameter ⊓ (graph2 InternalRawListRecursion.lookup upperValue i upperRow ⊓ (graph2 InternalRawListRecursion.lookup lowerValue j lowerRow)))))))))))
 have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨hv⟩ := square Q gamma count i j c parameter input upper upperParameter lower lowerParameter upperRow lowerRow upperValue lowerValue
  (andLeft h) (andLeft (andRight h)) (andLeft (andRight (andRight h))) (andLeft (andRight (andRight (andRight h)))) (andLeft (andRight (andRight (andRight (andRight h))))) (andLeft (andRight (andRight (andRight (andRight (andRight h)))))) (andLeft (andRight (andRight (andRight (andRight (andRight (andRight h))))))) (andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight h)))))))) (andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight h))))))))) (andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight h)))))))))) (andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight h))))))))))) (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight h)))))))))))
 exact ⟨Derivation.implicationIntroduction hv⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareProof
