module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationCoordinateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalBetaTotalityProof
open OriginalSourceNeutralApplication

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem tagValue (object function value : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right function object)))
    (ht : Nonempty (Derivation body Gamma (OriginalConstructorShape.tagGraph value function))) :
    Nonempty (Derivation body Gamma (graph1 objectTag value object)) :=
  unaryValue OriginalConstructorShape.tag InternalUnpair.right value function
    (Fin.cons object Fin.elim0) ht hr

theorem tagRecover (object function value : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right function object)))
    (ht : Nonempty (Derivation body Gamma (graph1 objectTag value object))) :
    Nonempty (Derivation body Gamma (OriginalConstructorShape.tagGraph value function)) :=
  unaryRecover OriginalConstructorShape.tag InternalUnpair.right value function
    (Fin.cons object Fin.elim0) ht hr

theorem nonLambdaForward (object function : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right function object)))
    (hn : Nonempty (Derivation body Gamma (nonLambdaObject object))) :
    Nonempty (Derivation body Gamma (OriginalNonLambdaApplication.nonLambda function)) := by
  obtain ⟨hr⟩ := hr
  obtain ⟨hn⟩ := hn
  let P := OriginalConstructorShape.tagGraph InternalOriginalStepGuard.one function
  have hp : Nonempty (Derivation body (P :: Gamma) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨ho⟩ := tagValue object function InternalOriginalStepGuard.one ⟨addHyp hr P⟩ hp
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination (addHyp hn P) ho)⟩

theorem nonLambdaBackward (object function : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right function object)))
    (hn : Nonempty (Derivation body Gamma (OriginalNonLambdaApplication.nonLambda function))) :
    Nonempty (Derivation body Gamma (nonLambdaObject object)) := by
  obtain ⟨hr⟩ := hr
  obtain ⟨hn⟩ := hn
  let P := graph1 objectTag InternalOriginalStepGuard.one object
  have hp : Nonempty (Derivation body (P :: Gamma) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := tagRecover object function InternalOriginalStepGuard.one ⟨addHyp hr P⟩ hp
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination (addHyp hn P) hf)⟩

/-- The Object premise observes exactly the internally exposed original
payload, with no decoding premise or new selection in the source tuple. -/
theorem nonLambdaIff (object function : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right function object))) :
    Nonempty (Derivation body Gamma
      ((nonLambdaObject object).iff (OriginalNonLambdaApplication.nonLambda function))) := by
  obtain ⟨hr⟩ := hr
  obtain ⟨hf⟩ := nonLambdaForward (Gamma := nonLambdaObject object :: Gamma)
    object function ⟨addHyp hr (nonLambdaObject object)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := nonLambdaBackward
    (Gamma := OriginalNonLambdaApplication.nonLambda function :: Gamma)
    object function ⟨addHyp hr (OriginalNonLambdaApplication.nonLambda function)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact andIntro ⟨Derivation.implicationIntroduction hf⟩ ⟨Derivation.implicationIntroduction hb⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationCoordinateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationCoordinateProof
