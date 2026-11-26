module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherTransitionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherRepeatProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (suc)
open InternalParameterizedBoundedDescentNormalizer InternalParameterizedNumericIteration
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- One genuine transition followed by an actually fixed value supplies the
original normalizer at its literal successor-of-input fuel. -/
theorem normalizerValue (R V : Program 2) (input fixed parameter : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (transitionGraph R V fixed input parameter)))
 (hf : Nonempty (Derivation body Delta (transitionGraph R V fixed fixed parameter))) :
 Nonempty (Derivation body Delta (normalizerGraph R V fixed input parameter)) := by
 have hrepeat := InternalParameterizedNumericIterationLawsProof.frontSuccBackward
   (transition R V) fixed input input fixed parameter hs
   (InternalParameterizedNumericIterationLawsProof.fixedValue (transition R V) input fixed parameter hf)
 apply compositionValue (repeatP (transition R V))
   (Fin.cons (.composition .succ (fun _ : Fin 1 => .projection (0 : Fin 2)))
      (Fin.cons (.projection (0 : Fin 2)) (Fin.cons (.projection (1 : Fin 2)) Fin.elim0)))
   fixed (Fin.cons input (Fin.cons parameter Fin.elim0))
   (Fin.cons (suc input) (Fin.cons input (Fin.cons parameter Fin.elim0))) hrepeat
 intro i
 refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => Fin.cases ?_ (fun x => Fin.elim0 x) l) k) i
 · apply compositionValue .succ (fun _ : Fin 1 => .projection (0 : Fin 2))
     (suc input) (Fin.cons input (Fin.cons parameter Fin.elim0)) (Fin.cons input Fin.elim0)
     (successorValue (Fin.cons input Fin.elim0))
   intro j
   obtain rfl := Fin.eq_zero j
   exact projectionValue 0 (Fin.cons input (Fin.cons parameter Fin.elim0))
 · exact projectionValue 0 (Fin.cons input (Fin.cons parameter Fin.elim0))
 · change Nonempty (Derivation body Delta (programGraph (.projection (1 : Fin 2)) parameter
     (Fin.cons input (Fin.cons parameter Fin.elim0))))
   exact projectionValue 1 (Fin.cons input (Fin.cons parameter Fin.elim0))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherRepeatProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherRepeatProof
