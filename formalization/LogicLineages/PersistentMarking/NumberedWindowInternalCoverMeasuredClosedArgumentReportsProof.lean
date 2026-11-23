module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedDirectedXTargets
public import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredClosedArgumentNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumeralEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredClosedArgumentReportsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalNumeralEvaluationProof (actualOriginalNumeralEvaluation)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalAuxExchangeMemoStepTargets (TermSyntaxCalibrated)
open NumberedWindowInternalAuxExchangeMemoStepChecks (exact_PhysicalAuxMemoExchange)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalCoverCombinedRestrictedDirectedXTargets (directedX)
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowExchangeAlgorithm (bits)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowInternalCoverMeasuredClosedArgumentNumericProof (exact_ClosedArgumentParentBit)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem evaluateClosedReport (p : Program 2) (left right : Nat)
    (run : evaluate p (List.Vector.ofFn ![left,right]) = 1) :
    Nonempty (Derivation body Γ
      (programGraph p (suc z) ![numeral left,numeral right])) := by
  have xs : (fun i => (numeral ((List.Vector.ofFn ![left,right]).get i) : OTerm α)) =
      ![numeral left,numeral right] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) i
  obtain ⟨result⟩ := actualOriginalNumeralEvaluation body 2 p (List.Vector.ofFn ![left,right]) α
  have one : (numeral 1 : OTerm α) = suc z := rfl
  rw [run,xs,one] at result
  unfold programGraph
  exact ⟨weakenClosed result Γ⟩

/-- The original physical base at the literal numeral parent tape. No
assertion is made at arbitrary symbolic raw coordinates. -/
theorem exact_ClosedArgumentBaseParentReport (s : Settings) (base : Program 2)
    (fit : ActualTermExchange s base) (dom cod fn a b : Nat)
    (moved : (bits s.equivalentHeads a b).1 = true)
    (left : (syntaxBits (auxRaw dom cod fn a)).1 = true)
    (right : (syntaxBits (auxRaw dom cod fn b)).1 = true) :
    Nonempty (Derivation body Γ (programGraph base (suc z)
      ![numeral (auxRaw dom cod fn a),numeral (auxRaw dom cod fn b)])) := by
  apply evaluateClosedReport
  exact (fit (auxRaw dom cod fn a) (auxRaw dom cod fn b)).trans
    (by simp only [exact_ClosedArgumentParentBit s.equivalentHeads dom cod fn a b moved left right,
      Bool.toNat_true])

/-- Instantiate only the exact installed directed callback. Its original
all-input calibration preserves the numeric base's argument branch. -/
theorem exact_ClosedArgumentDirectedParentReport (s : Settings) (base : Program 2) (V : Program 1)
    (fit : ActualTermExchange s base) (syntaxFit : TermSyntaxCalibrated V) (dom cod fn a b : Nat)
    (moved : (bits s.equivalentHeads a b).1 = true)
    (left : (syntaxBits (auxRaw dom cod fn a)).1 = true)
    (right : (syntaxBits (auxRaw dom cod fn b)).1 = true) :
    Nonempty (Derivation body Γ (programGraph (directedX base V) (suc z)
      ![numeral (auxRaw dom cod fn a),numeral (auxRaw dom cod fn b)])) := by
  exact exact_ClosedArgumentBaseParentReport s (directedX base V)
    (exact_PhysicalAuxMemoExchange s base V fit syntaxFit) dom cod fn a b moved left right

#print axioms exact_ClosedArgumentBaseParentReport
#print axioms exact_ClosedArgumentDirectedParentReport
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredClosedArgumentReportsProof
