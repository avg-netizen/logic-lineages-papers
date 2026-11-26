module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityLambdaBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityApplicationBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityRowsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalMixedTraceValidityDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rows (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (path : OTerm alpha) : Nonempty (Derivation body Delta
  (AtPath (OriginalTransparentMixedDirectBottom.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) path)) := by
 apply OriginalMixedTraceValidityRowsProof.rowsFromCore
 intro beta Theta code s t cert oldParam         hi hf
 apply OriginalMixedTraceValidityAssemblyProof.atCore H G M W oldStep
  _ code s t cert oldParam         hi hf
 intro xi Xi code head tail s t cert oldParam         hi hc hf
 exact OriginalMixedTraceValidityConsProof.atConsGeneric
  (OriginalTransparentMixedDirectBottom.source H G M W)
  (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
  (fun beta Theta path head tail s t cert oldParam         next out hi hc hf hg hl hr hz =>
    OriginalMixedTraceValidityLambdaBranchProof.lambdaBranch H G M W oldStep
     path head tail s t cert oldParam         next out hi hc hf hg hl hr hz)
  (fun beta Theta path head tail s t cert oldParam         next out hi hc hf hg hl hr hz =>
    OriginalMixedTraceValidityApplicationBranchProof.applicationBranch H G M W oldStep
     path head tail s t cert oldParam         next out hi hc hf hg hl hr hz)
  code head tail s t cert oldParam         hi hc hf


open InternalApplicationStepPeelSupportProof (andIntro)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof
open OriginalMixedTraceValidityBindingProof
open SourceComputabilityFormulaSupportProof (numeral)

theorem sourceFromRows (source : Program 2) (leaf : Program 4)
 (hrows : ∀ (beta : Type) (Theta : List (Formula beta)) (path : OTerm beta),
  Nonempty (Derivation body Theta (AtPath source leaf path)))
 (s t cert parameter : OTerm alpha)
 (h : Nonempty (Derivation body Delta
  (graph2 source (numeral 1) s parameter ⊓
   graph4 (OriginalMixedDirectBottomTrace.recognizes source leaf) (numeral 1) s t cert parameter))) :
 Nonempty (Derivation body Delta (result source leaf t parameter)) := by
 apply OriginalMixedTraceValidityZeroProof.typeCases cert (result source leaf t parameter)
 intro beta j Theta path incl hp
 rw [OriginalMixedTraceValiditySyntaxProof.resultRename]
 have h' := renameInto h j Theta incl
 simp only [OriginalUniverseDecoderInternalBooleanProof.andRename,graph2Rename,graph4Rename,
  OriginalRawSyntaxTransportInternalParserSyntaxProof.numeralRename] at h'
 exact atPathApply source leaf path (s.relabel j) (t.relabel j) (cert.relabel j) (parameter.relabel j)
  (hrows beta Theta path) (andIntro hp h')

theorem actualTargetSourceValidity : OriginalMixedTraceValidityTargets.ActualTargetSourceValidity := by
 intro H G M W oldStep body alpha Delta s t cert parameter
 let A : Formula alpha := graph2 (OriginalTransparentMixedDirectBottom.source H G M W) (numeral 1) s parameter ⊓
  graph4 (OriginalMixedDirectBottomTrace.recognizes (OriginalTransparentMixedDirectBottom.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)) (numeral 1) s t cert parameter
 have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨hr⟩ := sourceFromRows (OriginalTransparentMixedDirectBottom.source H G M W)
  (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
  (fun beta Theta path => rows (body := body) (Delta := Theta) H G M W oldStep path) s t cert parameter h
 exact ⟨Derivation.implicationIntroduction hr⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityProof
