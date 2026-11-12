module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceInductionZeroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceInductionAssemblyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (z eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalLambdaDirectBottomTraceInductionDefinitions
open OriginalLambdaDirectBottomTraceInductionSyntaxProof
open OriginalLambdaDirectBottomTraceInductionBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Conditional assembly only: the actual cons step is a visible proof
argument, to be supplied by the independent scoped lambda construction. -/
theorem atCore (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (consStep : ∀ (beta : Type) (Theta : List (Formula beta))
  (path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm beta),
  Nonempty (Derivation body Theta (BelowPath (OriginalTransparentDirectBottomGlobal.source p H G W)
   (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep path)) →
  Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode path head tail)) →
  Nonempty (Derivation body Theta (fields (OriginalTransparentDirectBottomGlobal.source p H G W)
   (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep path
   s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT)) →
  Nonempty (Derivation body Theta (result (OriginalTransparentDirectBottomGlobal.source p H G W)
   (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep s t newParam erasedS erasedT)))
 (path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath (OriginalTransparentDirectBottomGlobal.source p H G W)
   (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep path)))
 (hf : Nonempty (Derivation body Delta (fields (OriginalTransparentDirectBottomGlobal.source p H G W)
   (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep path
   s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT))) :
 Nonempty (Derivation body Delta (result (OriginalTransparentDirectBottomGlobal.source p H G W)
   (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep s t newParam erasedS erasedT)) := by
 let E : Formula alpha := eqn path z
 apply InternalOriginalPairingOrderArithmeticProof.formulaCases E _
 · have h := withHyp hf E
   have hp := outputTransport InternalUnpair.left path z (Fin.cons cert Fin.elim0)
    (show Nonempty (Derivation body (E :: Delta) (eqn path z)) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    (andLeft h)
   exact OriginalLambdaDirectBottomTraceInductionZeroProof.zeroAt p H G W P
    s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT (andIntro hp (andRight h))
 · apply OriginalContextInsertionLengthProof.nonzeroCases path _
    (show Nonempty (Derivation body (E.not :: Delta) E.not) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
   intro beta rho Theta head tail hrho hc
   rw [resultRename]
   have hi' := renameInto (withHyp hi E.not) rho Theta hrho
   have hf' := renameInto (withHyp hf E.not) rho Theta hrho
   rw [belowPathRename] at hi'
   rw [fieldsRename] at hf'
   exact consStep beta Theta (path.relabel rho) head tail (s.relabel rho) (t.relabel rho)
    (cert.relabel rho) (oldParam.relabel rho) (newParam.relabel rho) (gamma.relabel rho)
    (extended.relabel rho) (d.relabel rho) (cutoff.relabel rho) (c.relabel rho)
    (erasedS.relabel rho) (erasedT.relabel rho) hi' hc hf'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceInductionAssemblyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceInductionAssemblyProof
