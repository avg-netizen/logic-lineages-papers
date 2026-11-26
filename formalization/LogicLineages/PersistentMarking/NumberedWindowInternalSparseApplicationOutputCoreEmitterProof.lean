module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreEmitterProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePairGraphProof (consGraph)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (z rawCons)
open NumberedWindowInternalSparseApplicationOutputCore (seed)

abbrev objectTape {α : Type} (ctx dom cod fn arg y : OTerm α) : Fin 6 → OTerm α :=
  ![ctx,dom,cod,fn,arg,y]

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem emitCons (p q : Program 6) (h t : OTerm α) (xs : Fin 6 → OTerm α)
    (hp : Nonempty (Derivation body Γ (programGraph p h xs)))
    (hq : Nonempty (Derivation body Γ (programGraph q t xs))) :
    Nonempty (Derivation body Γ (programGraph (consOf p q) (rawCons h t) xs)) := by
  unfold consOf
  apply compositionValue fieldCons (Fin.cons p (Fin.cons q Fin.elim0))
    (rawCons h t) xs ![h,t] (consGraph h t)
  intro i
  exact Fin.cases hp (Fin.cases hq (fun e => Fin.elim0 e)) i

theorem seedGraph (ctx dom cod fn arg y : OTerm α) :
    Nonempty (Derivation body Γ (programGraph seed (auxiliaryTerm dom cod fn arg)
      (objectTape ctx dom cod fn arg y))) := by
  let v := objectTape ctx dom cod fn arg y
  let e := constantZero 6
  let aP : Program 6 := .projection 4
  let fP : Program 6 := .projection 3
  let cP : Program 6 := .projection 2
  let dP : Program 6 := .projection 1
  let aTail := consOf aP e
  let fTail := consOf fP aTail
  let cTail := consOf cP fTail
  let dTail := consOf dP cTail
  let aVal := rawCons arg z
  let fVal := rawCons fn aVal
  let cVal := rawCons cod fVal
  let dVal := rawCons dom cVal
  have ha : Nonempty (Derivation body Γ (programGraph aTail aVal v)) :=
    emitCons aP e arg z v (projectionValue 4 v) (constantZeroValue v)
  have hf : Nonempty (Derivation body Γ (programGraph fTail fVal v)) :=
    emitCons fP aTail fn aVal v (projectionValue 3 v) ha
  have hc : Nonempty (Derivation body Γ (programGraph cTail cVal v)) :=
    emitCons cP fTail cod fVal v (projectionValue 2 v) hf
  have hd : Nonempty (Derivation body Γ (programGraph dTail dVal v)) :=
    emitCons dP cTail dom cVal v (projectionValue 1 v) hc
  exact emitCons (literal 6 6) dTail (numeral 6) dVal v (literalGraph 6 v) hd

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreEmitterProof
