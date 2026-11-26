module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedBottomTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedDirectBottomProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomWrapperSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomSourceSpineProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedBottomProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalAcceptanceConjunctionProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalHereditaryLambdaGlobal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem introduction (H G : Program 1) (M W : Program 2) (oldStep : Program 4) (window : Program 1)
 (s t cert parameter typ : OTerm alpha)
 (h : Nonempty (Derivation body Delta (OriginalTransparentDirectBottom.Premises
  (OriginalTransparentMixedDirectBottom.source H G M W) s t cert parameter typ))) :
 Nonempty (Derivation body Delta (graph4 (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window)
  (suc z) s t cert parameter)) := by
 let endpoint := OriginalMixedLiteralEndpointDefinitions.endpoint H G M W
 let leaf := OriginalTransparentMixedDirectBottom.leaf H G M W oldStep
 let inner := wrapper endpoint window leaf
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 have hs := andLeft h
 have hn := andLeft (andRight h)
 have ht := andLeft (andRight (andRight h))
 have hb := andLeft (andRight (andRight (andRight h)))
 have hc := andRight (andRight (andRight (andRight h)))
 have hsp := OriginalTransparentDirectBottomSourceSpineProof.sourceSpine H G M W s t cert parameter typ hs hn hb
 have hleaf := OriginalTransparentMixedDirectBottomProof.introduction H G M W oldStep s t cert parameter typ h
 have hi := OriginalTransparentDirectBottomWrapperSupportProof.wrapperIntroduction endpoint window leaf
  s t cert parameter typ hn ht hb hsp hleaf
 have hg := OriginalTransparentVariableStepHereditaryProof.nilGuard inner s t cert parameter typ ht hb hc
 have hh := conjunctionAccept inner (OriginalHereditaryLambda.guard inner) xs hi hg
 exact OriginalTransparentDirectBottomWrapperSupportProof.wrapperIntroduction endpoint window
  (OriginalHereditaryLambda.refined inner) s t cert parameter typ hn ht hb hsp hh

theorem actualIntroduction : OriginalMixedClosedBottomTargets.ActualIntroduction := by
 intro H G M W oldStep window body alpha Delta s t cert parameter typ
 let A := OriginalTransparentDirectBottom.Premises (OriginalTransparentMixedDirectBottom.source H G M W) s t cert parameter typ
 obtain ⟨ho⟩ := introduction H G M W oldStep window s t cert parameter typ
  (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
 exact ⟨Derivation.implicationIntroduction ho⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedBottomProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedBottomProof
