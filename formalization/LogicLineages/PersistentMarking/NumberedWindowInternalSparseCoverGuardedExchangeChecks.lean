module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverGuardedExchangeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverGuardedExchangeNumericProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverGuardedExchangeChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseCoverScratch (coverOption)
open NumberedWindowInternalSparseScalarEdge (exchangeTape)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets
attribute [local irreducible] programGraph

theorem exact_OriginalExchangeCoverOption : ExactOriginalExchangeCoverOption :=
  NumberedWindowInternalSparseCoverGuardedExchangeNumericProof.preservesOption

theorem exact_GuardedExchangeCalibration : ExactGuardedExchangeCalibration :=
  NumberedWindowInternalSparseCoverGuardedExchangeNumericProof.calibration

private theorem slot {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (C : Program 3) (s : Settings) (i : Fin 2) (xs : Fin 2 → OTerm α) (out : OTerm α)
    (run : Nonempty (Derivation body Γ (unary (coverOption C s) out (xs i)))) :
    Nonempty (Derivation body Γ (programGraph (optionAtSlot C s i) out xs)) := by
  apply compositionValue (coverOption C s) (fun _ : Fin 1 => .projection i) out xs ![xs i] run
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue i xs

theorem exact_GuardedExchangeOptionEquality : ExactGuardedExchangeOptionEquality := by
  intro C s X body α Γ a b x y
  let xs := exchangeTape a b
  let accept := programGraph (guardedExchange C s X) (suc z) xs
  let outputs := unary (coverOption C s) x a ⊓ unary (coverOption C s) y b
  let Δ := (accept ⊓ outputs) :: Γ
  have h : Derivation body Δ (accept ⊓ outputs) := Derivation.hypothesis List.mem_cons_self
  obtain ⟨checks⟩ := conjunctionRecover X (compareOptions C s) xs ⟨Derivation.conjunctionLeft h⟩
  let r := Derivation.conjunctionRight h
  have calls (i : Fin 2) : Nonempty (Derivation body Δ (programGraph
      ((![optionAtSlot C s 0,optionAtSlot C s 1] : Fin 2 → Program 2) i)
      ((![x,y] : Fin 2 → OTerm α) i) xs)) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact slot C s 0 xs x ⟨Derivation.conjunctionLeft r⟩
    · obtain rfl := Fin.eq_zero j
      exact slot C s 1 xs y ⟨Derivation.conjunctionRight r⟩
  have compared := compositionRecover equalityTest ![optionAtSlot C s 0,optionAtSlot C s 1]
    (suc z) xs ![x,y] ⟨Derivation.conjunctionRight checks⟩ calls
  obtain ⟨same⟩ := equalityOfAcceptance x y compared
  exact ⟨Derivation.implicationIntroduction same⟩

#print axioms exact_OriginalExchangeCoverOption
#print axioms exact_GuardedExchangeCalibration
#print axioms exact_GuardedExchangeOptionEquality
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverGuardedExchangeChecks
