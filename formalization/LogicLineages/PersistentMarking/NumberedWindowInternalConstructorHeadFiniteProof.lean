module
public import LogicLineages.PersistentMarking.NumberedWindowInternalConstructorHeadFiniteTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanEqualityProof
import LogicLineages.PersistentMarking.NumberedWindowNumeralGraphChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalConstructorHeadFiniteProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply symm)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalListCodecEvaluationProof (consEvaluation)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedMultisetNumeric (numbersNumber)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowNumeralGraphChecks (exact_NumeralGraph)
open NumberedWindowNumeralGraphTargets (inputs)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (missGraph)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion)
open NumberedWindowInternalSparseRetainedScanEqualityProof (equalityOfHit)
open NumberedWindowInternalSparseScratchMembership (memberBase memberStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalConstructorHeadFiniteTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem closedCell (n : Nat) (rest : List Nat) :
    D B Γ (consGraph (numeral (numbersNumber (n :: rest))) (numeral n) (numeral (numbersNumber rest))) := by
  let xs := n ::ᵥ numbersNumber rest ::ᵥ List.Vector.nil
  have cell := exact_NumeralGraph 2 consCode xs B α Γ
  have tape : (inputs xs : Fin 2 → OTerm α) =
      Fin.cons (numeral n) (Fin.cons (numeral (numbersNumber rest)) Fin.elim0) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  rw [tape] at cell
  simpa only [xs,consEvaluation,numbersNumber] using cell

private theorem noEmpty (head : OTerm α) (win : D B Γ (memberGraph z head)) :
    D B Γ (⊥ : Formula α) := by
  have impossible := nilRecover memberBase memberStep (suc z) ![head] win
  have z0 : D B Γ (programGraph memberBase z ![head]) := constantZeroValue ![head]
  obtain ⟨e⟩ := valueUnique memberBase (suc z) z ![head] impossible z0
  exact ⟨sucNeZeroApply e⟩

/-- Finite dispatch of an actually admitted head occurrence. Only the
literal closed constructor graph is calibrated via the proved numeral
equations; the selected head remains an arbitrary object term. -/
theorem exact_OpenConstructorHeadFiniteCases : ExactOpenConstructorHeadFiniteCases := by
  intro heads
  induction heads with
  | nil =>
    intro B α Γ head goal present _
    obtain ⟨bad⟩ := noEmpty head present
    exact ⟨Derivation.explosion bad⟩
  | cons n rest ih =>
    intro B α Γ head goal present next
    let test := (missGraph (numeral n) head).not
    let tail := memberGraph (numeral (numbersNumber rest)) head
    obtain ⟨choices⟩ := consInversion (numeral (numbersNumber (n :: rest))) (numeral n)
      (numeral (numbersNumber rest)) head (closedCell n rest) present
    have atHead : D B Γ (test.imp goal) := by
      have live : D B (test :: Γ) test := ⟨Derivation.hypothesis List.mem_cons_self⟩
      obtain ⟨eq⟩ := equalityOfHit (numeral n) head live
      obtain ⟨d⟩ := next n List.mem_cons_self
      have rule : D B Γ ((eqn head (numeral n)).imp goal) :=
        ⟨Derivation.implicationIntroduction d⟩
      obtain ⟨rule'⟩ := withHyp rule test
      exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination rule' (symm eq))⟩
    have atTail : D B Γ (tail.imp goal) := by
      have live : D B (tail :: Γ) tail := ⟨Derivation.hypothesis List.mem_cons_self⟩
      obtain ⟨d⟩ := ih B α (tail :: Γ) head goal live (fun k hk => by
        obtain ⟨e⟩ := next k (List.mem_cons_of_mem _ hk)
        have rule : D B Γ ((eqn head (numeral k)).imp goal) :=
          ⟨Derivation.implicationIntroduction e⟩
        obtain ⟨rule⟩ := withHyp (withHyp rule tail) (eqn head (numeral k))
        exact ⟨Derivation.implicationElimination rule (Derivation.hypothesis List.mem_cons_self)⟩)
      exact ⟨Derivation.implicationIntroduction d⟩
    obtain ⟨l⟩ := atHead
    obtain ⟨r⟩ := atTail
    exact ⟨disjunctionElimination choices l r⟩

#print axioms exact_OpenConstructorHeadFiniteCases

end LogicLineages.PersistentMarking.NumberedWindowInternalConstructorHeadFiniteProof
