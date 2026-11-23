module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsMapTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsMap
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalRawListRecursion (recGraph consStep)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalRawListRecursionProof
  (actualOriginalListRecursionZero actualOriginalListRecursionCons)
open NumberedWindowInternalDirectInsertedTargetsMapTargets

theorem exactOpenTargetMapNil (B : Positive (Fin 1)) (α : Type)
    (out : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation B []
      ((recGraph targetBase targetStep out OrdinaryArithmetic.zeroTerm Fin.elim0).iff
        (programGraph targetBase out Fin.elim0))) :=
  actualOriginalListRecursionZero B 0 targetBase targetStep α out Fin.elim0

theorem exactOpenTargetMapCons (B : Positive (Fin 1)) (α : Type)
    (code head tail out : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation B []
      ((programGraph consCode code (Fin.cons head (Fin.cons tail Fin.elim0))).imp
        ((recGraph targetBase targetStep out code Fin.elim0).iff
          (consStep targetBase targetStep out head tail Fin.elim0)))) :=
  actualOriginalListRecursionCons B 0 targetBase targetStep α code head tail out Fin.elim0

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsMap
