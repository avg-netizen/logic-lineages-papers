module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomSourceSpineTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomNonApplicationSpineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomApplicationSpineProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomSourceSpineProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalAcceptanceSupportProof InternalControlGraphSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem sourceSpine (H G : Program 1) (M W : Program 2) (s t cert parameter typ : OTerm alpha)
    (hs : Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.source H G M W) InternalOriginalStepGuard.one s parameter)))
    (hn : Nonempty (Derivation body Delta (BottomRepresentative.bottomGraph InternalOriginalStepGuard.one s).not))
    (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode t typ))) :
    Nonempty (Derivation body Delta
      (graph4 (PositiveGuard.spineGuard BottomSpineMeasure.measure) InternalOriginalStepGuard.one s t cert parameter)) := by
  let A := graph1 OriginalLambdaConstructor.tag (numeral 2) s
  apply formulaCases A
  · exact OriginalTransparentDirectBottomApplicationSpineProof.applicationSpine s t cert parameter typ
      (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (withHyp hb A)
  · have h3 := OriginalTransparentDirectBottomSourceProof.concreteSourceNotTagThree H G M W s parameter
      (withHyp hs A.not) (withHyp hn A.not)
    exact OriginalTransparentDirectBottomNonApplicationSpineProof.nonApplicationSpine s t cert parameter
      (show Nonempty (Derivation body (A.not :: Delta) A.not) from ⟨Derivation.hypothesis List.mem_cons_self⟩) h3

theorem actualConcreteSourceBottomSpine :
    OriginalTransparentDirectBottomSourceSpineTargets.ActualConcreteSourceBottomSpine := by
  intro H G M W body alpha Delta s t cert parameter typ
  let A := graph2 (OriginalUniverseDecoder.source H G M W) InternalOriginalStepGuard.one s parameter ⊓
    ((BottomRepresentative.bottomGraph InternalOriginalStepGuard.one s).not ⊓ graph1 BottomRepresentative.bottomCode t typ)
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hout⟩ := sourceSpine H G M W s t cert parameter typ (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction hout⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomSourceSpineProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomSourceSpineProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomSourceSpineProof.actualConcreteSourceBottomSpine
