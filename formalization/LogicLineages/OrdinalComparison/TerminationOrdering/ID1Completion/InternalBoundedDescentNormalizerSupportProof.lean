module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalBoundedDescentNormalizer InternalBoundedDescentNormalizerSyntaxProof
open InternalNumericIteration InternalNumericIterationSyntaxProof InternalNumericIterationSupportProof
open InternalNumericIterationFixedPointProof InternalNumericIterationProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalQuotientComparisonProof
open InternalSquareRootArithmeticSupportProof InternalUnpairReverseBoundsArithmeticProof
open InternalLeastNumberProof InternalSourceInversionSupportProof InternalBetaTotalityProof
open InternalPositiveUnfoldingSupportProof
open SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem atMostZero (value : OTerm α)
    (h : Nonempty (Derivation body Gamma (atMost value z))) :
    Nonempty (Derivation body Gamma (eqn value z)) := by
  obtain ⟨h⟩ := h
  obtain ⟨split⟩ := actualRightSuccessorSplit body α value z
  rw [onEquality] at split
  have hd := Derivation.implicationElimination (weakenClosed split Gamma) h
  obtain ⟨hn⟩ := actualNothingBelowZero body α value
  have hl : Derivation body Gamma ((ltF value z).imp (eqn value z)) :=
    Derivation.implicationIntroduction (Derivation.explosion
      (Derivation.implicationElimination (weakenClosed hn _) (Derivation.hypothesis List.mem_cons_self)))
  have he : Derivation body Gamma ((eqn value z).imp (eqn value z)) :=
    Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)
  exact ⟨disjunctionElimination hd hl he⟩

theorem boundOfSplit (out input : OTerm α)
    (h : Nonempty (Derivation body Gamma (eqn out input ⊔ ltF out input))) :
    Nonempty (Derivation body Gamma (atMost out input)) := by
  obtain ⟨h⟩ := h
  have he : Derivation body Gamma ((eqn out input).imp (atMost out input)) :=
    Derivation.implicationIntroduction (equalToNext (Derivation.hypothesis List.mem_cons_self))
  obtain ⟨hl⟩ := rightSuccessor (body := body) (Gamma := ltF out input :: Gamma)
    out input ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination h he (Derivation.implicationIntroduction hl)⟩

theorem unaryInput (p : Program 1) (out input other : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn input other)))
    (h : Nonempty (Derivation body Gamma (unaryGraph p out input))) :
    Nonempty (Derivation body Gamma (unaryGraph p out other)) :=
  headTransport p out input other Fin.elim0 he h

theorem fixedTransport (R V : Program 1) (fixed other : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn fixed other)))
    (h : Nonempty (Derivation body Gamma (transitionGraph R V fixed fixed))) :
    Nonempty (Derivation body Gamma (transitionGraph R V other other)) :=
  outputTransport (transition R V) fixed other (Fin.cons other Fin.elim0) he
    (headTransport (transition R V) fixed fixed other Fin.elim0 he h)

theorem repeatFixedResult (R V : Program 1) (count fixed out : OTerm α)
    (hf : Nonempty (Derivation body Gamma (transitionGraph R V fixed fixed)))
    (ho : Nonempty (Derivation body Gamma (repeatGraph (transition R V) out count fixed))) :
    Nonempty (Derivation body Gamma (transitionGraph R V out out)) := by
  have hfix := fixedValue (transition R V) count fixed hf
  have he := valueUnique (repeatProgram (transition R V)) fixed out
    (Fin.cons count (Fin.cons fixed Fin.elim0)) hfix ho
  exact fixedTransport R V fixed out he hf

theorem normalizerRecover (R V : Program 1) (out input : OTerm α)
    (h : Nonempty (Derivation body Gamma (normalizerGraph R V out input))) :
    Nonempty (Derivation body Gamma (repeatGraph (transition R V) out (suc input) input)) := by
  apply compositionRecover (repeatProgram (transition R V))
    (Fin.cons .succ (Fin.cons (.projection (0 : Fin 1)) Fin.elim0)) out
    (Fin.cons input Fin.elim0) (Fin.cons (suc input) (Fin.cons input Fin.elim0)) h
  intro i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => Fin.elim0 k) i) i
  · exact successorValue (Fin.cons input Fin.elim0)
  · exact projectionValue (0 : Fin 1) (Fin.cons input Fin.elim0)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerSupportProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerSupportProof
