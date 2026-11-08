module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedBoundedDescentNormalizer InternalParameterizedBoundedDescentNormalizerSyntaxProof
open InternalParameterizedNumericIteration
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The weak value order is the same original arithmetic formula as before. -/
theorem atMostZero (value : OTerm α)
    (h : Nonempty (Derivation body Gamma (atMost value z))) :
    Nonempty (Derivation body Gamma (eqn value z)) :=
  InternalBoundedDescentNormalizerSupportProof.atMostZero value h

theorem boundOfSplit (out input : OTerm α)
    (h : Nonempty (Derivation body Gamma (eqn out input ⊔ InternalOriginalOrderSyntaxProof.ltF out input))) :
    Nonempty (Derivation body Gamma (atMost out input)) :=
  InternalBoundedDescentNormalizerSupportProof.boundOfSplit out input h

/-- Transport only the VALUE input; the binary program and parameter are unchanged. -/
theorem binaryInput (p : Program 2) (out input other parameter : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn input other)))
    (h : Nonempty (Derivation body Gamma (binaryGraph p out input parameter))) :
    Nonempty (Derivation body Gamma (binaryGraph p out other parameter)) :=
  headTransport p out input other (Fin.cons parameter Fin.elim0) he h

theorem fixedTransport (R V : Program 2) (fixed other parameter : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn fixed other)))
    (h : Nonempty (Derivation body Gamma (transitionGraph R V fixed fixed parameter))) :
    Nonempty (Derivation body Gamma (transitionGraph R V other other parameter)) :=
  outputTransport (transition R V) fixed other (Fin.cons other (Fin.cons parameter Fin.elim0)) he
    (headTransport (transition R V) fixed fixed other (Fin.cons parameter Fin.elim0) he h)

theorem repeatFixedResult (R V : Program 2) (count fixed out parameter : OTerm α)
    (hf : Nonempty (Derivation body Gamma (transitionGraph R V fixed fixed parameter)))
    (ho : Nonempty (Derivation body Gamma (repeatGraph (transition R V) out count fixed parameter))) :
    Nonempty (Derivation body Gamma (transitionGraph R V out out parameter)) := by
  have hfix := InternalParameterizedNumericIterationLawsProof.fixedValue
    (transition R V) count fixed parameter hf
  have he := valueUnique (repeatP (transition R V)) fixed out
    (Fin.cons count (Fin.cons fixed (Fin.cons parameter Fin.elim0))) hfix ho
  exact fixedTransport R V fixed out parameter he hf

/-- Recover the actual repeatP graph at [successor input,input,parameter].
The fuel is the original value successor, never the encoded carried state. -/
theorem normalizerRecover (R V : Program 2) (out input parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (normalizerGraph R V out input parameter))) :
    Nonempty (Derivation body Gamma
      (repeatGraph (transition R V) out (suc input) input parameter)) := by
  apply compositionRecover (repeatP (transition R V))
    (Fin.cons (.composition .succ (fun _ : Fin 1 => .projection (0 : Fin 2)))
      (Fin.cons (.projection (0 : Fin 2))
        (Fin.cons (.projection (1 : Fin 2)) Fin.elim0))) out
    (Fin.cons input (Fin.cons parameter Fin.elim0))
    (Fin.cons (suc input) (Fin.cons input (Fin.cons parameter Fin.elim0))) h
  intro i
  refine Fin.cases ?_ (fun i => Fin.cases ?_
    (fun i => Fin.cases ?_ (fun k => Fin.elim0 k) i) i) i
  · apply compositionValue .succ (fun _ : Fin 1 => .projection (0 : Fin 2))
      (suc input) (Fin.cons input (Fin.cons parameter Fin.elim0))
      (Fin.cons input Fin.elim0) (successorValue (Fin.cons input Fin.elim0))
    intro j
    obtain rfl := Fin.eq_zero j
    exact projectionValue (0 : Fin 2) (Fin.cons input (Fin.cons parameter Fin.elim0))
  · exact projectionValue (0 : Fin 2) (Fin.cons input (Fin.cons parameter Fin.elim0))
  · exact projectionValue (1 : Fin 2) (Fin.cons input (Fin.cons parameter Fin.elim0))

/-- Zero-fuel recovery is valid at an arbitrary symbolic parameter. -/
theorem repeatZeroRecover (P : Program 2) (out input parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (repeatGraph P out z input parameter))) :
    Nonempty (Derivation body Gamma (eqn out input)) :=
  valueUnique (repeatP P) out input (Fin.cons z (Fin.cons input (Fin.cons parameter Fin.elim0)))
    h (InternalParameterizedNumericIterationLawsProof.zeroValue P input parameter)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerSupportProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerSupportProof
