module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantApplicationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalCanonicalQuotientEdgeSelection InternalCanonicalQuotientEdgeSelectionTargets
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalAcceptanceConjunctionProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The two actual W conjuncts, with the target projection eliminated. -/
theorem stepRecover (data : InternalCanonicalDescentSelection.Data)
    (s t k : OTerm α)
    (h : Nonempty (Derivation body Gamma (stepAccepted data s t k))) :
    Nonempty (Derivation body Gamma
      (InternalOriginalApplicationStep.accepted (baseData data) s t k ⊓
        graph1 (InternalCanonicalDescentSelection.validity data).sourceValid
          InternalOriginalStepGuard.one t)) := by
  let xs : Fin 3 → OTerm α := Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))
  have hr := conjunctionRecover
    (InternalOriginalApplicationStep.stepChecker (baseData data))
    (targetSourceValidityAt data) xs h
  exact andIntro (andLeft hr)
    (unaryRecover (InternalCanonicalDescentSelection.validity data).sourceValid
      (.projection 1) InternalOriginalStepGuard.one t xs (andRight hr)
      (projectionValue 1 xs))

theorem stepAccept (data : InternalCanonicalDescentSelection.Data)
    (s t k : OTerm α)
    (hs : Nonempty (Derivation body Gamma
      (InternalOriginalApplicationStep.accepted (baseData data) s t k)))
    (ht : Nonempty (Derivation body Gamma
      (graph1 (InternalCanonicalDescentSelection.validity data).sourceValid
        InternalOriginalStepGuard.one t))) :
    Nonempty (Derivation body Gamma (stepAccepted data s t k)) := by
  let xs : Fin 3 → OTerm α := Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))
  exact conjunctionAccept
    (InternalOriginalApplicationStep.stepChecker (baseData data))
    (targetSourceValidityAt data) xs hs
    (unaryValue (InternalCanonicalDescentSelection.validity data).sourceValid
      (.projection 1) InternalOriginalStepGuard.one t xs ht (projectionValue 1 xs))

/-- Base acceptance lifts by its checked rule. W's additional V(t), with
the actual endpoint graphs, closes the target application's SOURCE validity. -/
theorem applicationStep (data : InternalCanonicalDescentSelection.Data)
    (arrow d e s t a k sourceApp targetApp liftedStep : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (InternalOriginalApplicationStep.liftPremises (baseData data)
        arrow d e s t a k sourceApp targetApp liftedStep)))
    (hw : Nonempty (Derivation body Gamma (stepAccepted data s t k))) :
    Nonempty (Derivation body Gamma
      (stepAccepted data sourceApp targetApp liftedStep)) := by
  have hs := stepRecover data s t k hw
  have hb := InternalOriginalApplicationStepSupportProof.applicationStep (baseData data)
    arrow d e s t a k sourceApp targetApp liftedStep hp (andLeft hs)
  have he := andLeft hp
  have har := andLeft he
  have hr := InternalStructuralEndpointGuardSupportProof.endpointRecover
    (InternalCanonicalDescentSelection.validity data) data.member
    arrow d e s t a har (andLeft (andRight he))
  have htags := andLeft (andRight (andRight (andRight hr)))
  have hv := InternalCanonicalResultFoldInvariantApplicationSupportProof.rawValidity
    data.oldValidity data.member arrow d e t a targetApp har
    (andLeft (andRight htags)) (andRight (andRight htags))
    (andRight (andRight (andRight (andRight hr))))
    (andRight hs) (andLeft (andRight (andRight hr)))
    (andRight (andRight (andRight he)))
  exact stepAccept data sourceApp targetApp liftedStep hb hv

theorem actualOriginalCanonicalEdgeApplicationStep : ActualOriginalCanonicalEdgeApplicationStep := by
  intro body data α Delta arrow d e s t a k sourceApp targetApp liftedStep
  let premise := InternalOriginalApplicationStep.liftPremises (baseData data)
    arrow d e s t a k sourceApp targetApp liftedStep ⊓ stepAccepted data s t k
  have hp : Nonempty (Derivation body (premise :: Delta) premise) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := applicationStep data arrow d e s t a k sourceApp targetApp liftedStep
    (andLeft hp) (andRight hp)
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionSupportProof
