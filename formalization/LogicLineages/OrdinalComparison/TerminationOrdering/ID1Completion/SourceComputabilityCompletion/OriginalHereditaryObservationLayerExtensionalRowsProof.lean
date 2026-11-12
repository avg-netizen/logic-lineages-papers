module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerExtensionalCellProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsBoundProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerExtensionalRowsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalTagArithmeticSyntaxProof (emb)
open OriginalTypedDecoderInternalLogicSyntaxProof
open OriginalTypedArgumentObservationsCongruence OriginalTypedArgumentObservationsCongruenceAgreementProof
open OriginalRootObservationExtensional OriginalRootObservationExtensionalCallProof
open OriginalHereditaryDeletionRows OriginalHereditaryDeletionRowsObserverCongruence
open OriginalHereditaryDeletionRowsObserverCongruenceSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rowsAt (Q T : Program 2) (input parameter left right : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (GlobalAgreement Q T)))
 (hl : Nonempty (Derivation body Delta (graph2 (rows Q) left input parameter)))
 (hr : Nonempty (Derivation body Delta (graph2 (rows T) right input parameter))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 let g : Program 2 := rightOf (.projection 1)
 let c : Program 2 := .composition OriginalContextInsertion.length (fun _ : Fin 1 => g)
 let qs : Fin 2 → Program 2 := ![g,c]
 let xs : Fin 2 → OTerm alpha := ![input,parameter]
 apply queryCases qs xs _
 intro beta rho ys Theta hrho hq
 rw [equalRename]
 let xx : Fin 2 → OTerm beta := ![input.relabel rho,parameter.relabel rho]
 have he : (fun i => (xs i).relabel rho) = xx := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [he] at hq
 have hGamma := unaryRecover InternalUnpair.right (.projection 1) (ys 0) (parameter.relabel rho) xx (hq 0) (InternalControlGraphSupportProof.projectionValue 1 xx)
 have hCount := unaryRecover OriginalContextInsertion.length g (ys 1) (ys 0) xx (hq 1) (hq 0)
 have hg' := renameInto hg rho Theta hrho
 rw [globalRename] at hg'
 have hl' := renameInto hl rho Theta hrho
 have hr' := renameInto hr rho Theta hrho
 rw [graph2Rename] at hl' hr'
 have hs := OriginalHereditaryDeletionRowsBoundProof.scanFromRows Q (input.relabel rho) (parameter.relabel rho) (ys 0) (ys 1) (left.relabel rho) hGamma hCount hl'
 have ht := OriginalHereditaryDeletionRowsBoundProof.scanFromRows T (input.relabel rho) (parameter.relabel rho) (ys 0) (ys 1) (right.relabel rho) hGamma hCount hr'
 have hc := OriginalHereditaryObservationLayerExtensionalCellProof.cells Q T (ys 1) (input.relabel rho) (parameter.relabel rho) hg'
 obtain ⟨h⟩ := OriginalHereditaryDeletionRowsObserverCongruenceProof.exactCongruence Q T body beta Theta
  (ys 1) (input.relabel rho) (parameter.relabel rho) (input.relabel rho) (parameter.relabel rho) (left.relabel rho) (right.relabel rho)
 obtain ⟨hp⟩ := andIntro hc (andIntro hs ht)
 exact ⟨Derivation.implicationElimination h hp⟩

theorem rowsAgreement (Q T : Program 2) (parameter : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (GlobalAgreement Q T))) :
 Nonempty (Derivation body Delta (Agreement (rows Q) (rows T) parameter)) := by
 apply agreementIntro _ _ parameter
 intro beta rho Theta input left right hrho hl hr
 have hg' := renameInto hg rho Theta hrho
 rw [globalRename] at hg'
 exact rowsAt Q T input (parameter.relabel rho) left right hg' hl hr

theorem exactRows : OriginalHereditaryObservationLayerExtensionalTargets.RowsExtensionality := by
 intro Q T body alpha Delta parameter
 let A : Formula alpha := GlobalAgreement Q T
 obtain ⟨h⟩ := rowsAgreement Q T parameter (body := body) (Delta := A :: Delta) ⟨Derivation.hypothesis List.mem_cons_self⟩
 exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerExtensionalRowsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerExtensionalRowsProof
