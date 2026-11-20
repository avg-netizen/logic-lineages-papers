module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterValueProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalFreshProbeEmitter NumberedWindowInternalFreshProbeEmitterNumericTargets
open NumberedWindowInternalFreshProbeDispatchProgram (zeroAt literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (compositeTwo compositeThree zeroEvaluation literalEvaluation)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowFieldAlgorithm (pack packNode)
open NumberedWindowFreeAddress (freeAddress)

private theorem consOfValue {n : Nat} (p q : Program n) (xs : List.Vector Nat n) :
    evaluate (consOf p q) xs = pair (evaluate p xs) (evaluate q xs) + 1 := by
  rw [consOf,compositeTwo]
  exact NumberedWindowInternalSparsePairEvaluationProof.consValue _ _

theorem packedEmitterValue (c t n : Nat) :
    evaluate packedEmitter (c ::ᵥ t ::ᵥ n ::ᵥ nil) = packedFree c t n := by
  let xs := c ::ᵥ t ::ᵥ n ::ᵥ nil
  have h0 : evaluate (.projection (0 : Fin 3)) xs = c := rfl
  have h1 : evaluate (.projection (1 : Fin 3)) xs = t := rfl
  have h2 : evaluate (.projection (2 : Fin 3)) xs = n := rfl
  change evaluate packedEmitter xs = _
  simp only [packedEmitter,consOfValue,h0,h1,h2,zeroEvaluation,literalEvaluation,
    packedFree,packNode,pack]

theorem emitSelectedValue (p : Selectors) (q : Nat) :
    evaluate (emitSelected p) (q ::ᵥ nil) =
      packedFree (evaluate p.context (q ::ᵥ nil)) (evaluate p.domain (q ::ᵥ nil))
        (evaluate p.name (q ::ᵥ nil)) := by
  rw [emitSelected,compositeThree,packedEmitterValue]

theorem exactPackedFree : ExactPackedFreeEmitterValue :=
  ⟨packedEmitterValue,fun Γ t n => packedEmitterValue (pack Γ) t n⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterValueProof
