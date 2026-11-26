module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedDirectBottomTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathNilProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepHereditaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedDirectBottomProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem introduction (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (s t cert parameter typ : OTerm alpha)
 (hh : Nonempty (Derivation body Delta (OriginalTransparentDirectBottom.Premises
  (OriginalTransparentMixedDirectBottom.source H G M W) s t cert parameter typ))) :
 Nonempty (Derivation body Delta (graph4 (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
  InternalOriginalStepGuard.one s t cert parameter)) := by
 have hc := andRight (andRight (andRight (andRight hh)))
 have hp := OriginalTransparentVariableStepHereditaryProof.certificatePath s cert hc
 have ho := OriginalTransparentDirectBottomInternalProof.introduction
  (OriginalTransparentMixedDirectBottom.source H G M W) oldStep s t cert typ parameter
  (andLeft hh) (andLeft (andRight hh)) (andLeft (andRight (andRight hh)))
  (andLeft (andRight (andRight (andRight hh)))) hc
 exact OriginalTransparentMixedPathNilProof.introduction (OriginalTransparentMixedDirectBottom.source H G M W)
  (OriginalTransparentDirectBottom.refined (OriginalTransparentMixedDirectBottom.source H G M W) oldStep)
  InternalOriginalStepGuard.one s t cert parameter hp ho

theorem actualIntroduction : OriginalTransparentMixedDirectBottomTargets.ActualIntroduction := by
 intro H G M W oldStep body alpha Delta s t cert parameter typ
 let A := OriginalTransparentDirectBottom.Premises (OriginalTransparentMixedDirectBottom.source H G M W) s t cert parameter typ
 obtain ⟨ho⟩ := introduction H G M W oldStep s t cert parameter typ
  (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
 exact ⟨Derivation.implicationIntroduction ho⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedDirectBottomProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedDirectBottomProof
