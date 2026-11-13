module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyDomainClosureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyFieldSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedImplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaWindowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyDomainClosureSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAcceptanceSupportProof InternalControlGraphSupportProof
open InternalAcceptanceConjunctionProof
open UniformCertificateCompletion EvaluatorKeyPut
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem factors (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (input parameter : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (Domain p H G W input parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (BottomRepresentative.windowAt (prepared p H G W).window) (numeral 1) input parameter ⊓
       graph2 (OriginalUniverseDecoder.source H G (member p H G W) W) (numeral 1) input parameter)) := by
  have ha := andRight hd
  change Nonempty (Derivation body Delta
    (graph2 (OriginalActiveObservedClass.activation (prepared p H G W) H G W)
      (numeral 1) input parameter)) at ha
  rw [OriginalStructuralTraversalKeyFieldSupportProof.activation] at ha
  exact conjunctionRecover _ _ (Fin.cons input (Fin.cons parameter Fin.elim0)) ha

theorem assemble (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (input parameter : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (graph2 (BottomRepresentative.windowAt (prepared p H G W).window) (numeral 1) input parameter)))
    (hs : Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.source H G (member p H G W) W) (numeral 1) input parameter))) :
    Nonempty (Derivation body Delta (Domain p H G W input parameter)) := by
  have ht := OriginalTransparentDecoderValidatorCollapsePackedImplicationProof.sourceToTarget
    H G (member p H G W) W input parameter hs
  have ha : Nonempty (Derivation body Delta
    (graph2 (OriginalActiveObservedClass.activation (prepared p H G W) H G W)
      (numeral 1) input parameter)) := by
    rw [OriginalStructuralTraversalKeyFieldSupportProof.activation]
    exact conjunctionAccept _ _ (Fin.cons input (Fin.cons parameter Fin.elim0)) hw hs
  exact andIntro ht ha

theorem sameOuterWindow (window : Program 1)
    (input out oldParameter newParameter c extended gamma : OTerm alpha)
    (hop : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing oldParameter c extended)))
    (hnp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newParameter c gamma)))
    (hw : Nonempty (Derivation body Delta
      (graph2 (BottomRepresentative.windowAt window) (numeral 1) input oldParameter))) :
    Nonempty (Derivation body Delta
      (graph2 (BottomRepresentative.windowAt window) (numeral 1) out newParameter)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons oldParameter Fin.elim0)
  let ys : Fin 2 → OTerm alpha := Fin.cons out (Fin.cons newParameter Fin.elim0)
  have hx := unaryValue InternalUnpair.left (.projection 1) c oldParameter xs
    (pairLeft oldParameter c extended hop) (projectionValue 1 xs)
  have hy := unaryValue InternalUnpair.left (.projection 1) c newParameter ys
    (pairLeft newParameter c gamma hnp) (projectionValue 1 ys)
  exact unaryValue window (leftOf (.projection 1)) (numeral 1) c ys
    (unaryRecover window (leftOf (.projection 1)) (numeral 1) c xs hw hx) hy
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyDomainClosureSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyDomainClosureSupportProof
