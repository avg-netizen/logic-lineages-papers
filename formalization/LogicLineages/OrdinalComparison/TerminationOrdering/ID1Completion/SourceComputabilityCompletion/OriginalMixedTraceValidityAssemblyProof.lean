module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityZeroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityAssemblyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (z eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalMixedTraceValidityDefinitions
open OriginalMixedTraceValiditySyntaxProof
open OriginalMixedTraceValidityBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Conditional assembly only: the actual cons step is a visible proof
argument, to be supplied by the independent scoped mixed-prefix construction. -/
theorem atCore (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (consStep : ∀ (beta : Type) (Theta : List (Formula beta))
  (path head tail s t cert oldParam         : OTerm beta),
  Nonempty (Derivation body Theta (BelowPath (OriginalTransparentMixedDirectBottom.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) path)) →
  Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode path head tail)) →
  Nonempty (Derivation body Theta (fields (OriginalTransparentMixedDirectBottom.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) path
   s t cert oldParam        )) →
  Nonempty (Derivation body Theta (result (OriginalTransparentMixedDirectBottom.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) t oldParam)))
 (path s t cert oldParam         : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath (OriginalTransparentMixedDirectBottom.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) path)))
 (hf : Nonempty (Derivation body Delta (fields (OriginalTransparentMixedDirectBottom.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) path
   s t cert oldParam        ))) :
 Nonempty (Derivation body Delta (result (OriginalTransparentMixedDirectBottom.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) t oldParam)) := by
 let E : Formula alpha := eqn path z
 apply InternalOriginalPairingOrderArithmeticProof.formulaCases E _
 · have h := withHyp hf E
   have hp := outputTransport InternalUnpair.left path z (Fin.cons cert Fin.elim0)
    (show Nonempty (Derivation body (E :: Delta) (eqn path z)) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    (andLeft h)
   exact OriginalMixedTraceValidityZeroProof.zeroAt H G M W oldStep
    s t cert oldParam         (andIntro hp (andRight h))
 · apply OriginalContextInsertionLengthProof.nonzeroCases path _
    (show Nonempty (Derivation body (E.not :: Delta) E.not) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
   intro beta rho Theta head tail hrho hc
   rw [resultRename]
   have hi' := renameInto (withHyp hi E.not) rho Theta hrho
   have hf' := renameInto (withHyp hf E.not) rho Theta hrho
   rw [belowPathRename] at hi'
   rw [fieldsRename] at hf'
   exact consStep beta Theta (path.relabel rho) head tail (s.relabel rho) (t.relabel rho)
    (cert.relabel rho) (oldParam.relabel rho)  
       
      hi' hc hf'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityAssemblyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityAssemblyProof
