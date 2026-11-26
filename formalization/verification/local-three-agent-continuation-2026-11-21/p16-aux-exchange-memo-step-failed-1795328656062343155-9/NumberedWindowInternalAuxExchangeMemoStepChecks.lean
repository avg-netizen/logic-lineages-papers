module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepChecks
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (conjunction)
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalRawListRecursion (lookup)
open NumberedWindowPairAlgorithm (pair decode)
open NumberedWindowInternalAuxExchangeMemoTargets (stepValue guardedAuxChildren)
open NumberedWindowInternalAuxExchangeMemoChecks (exact_AuxExchangeMemoCalibration)
open NumberedWindowInternalAuxExchangeMemoStepTargets
open NumberedWindowInternalAuxExchangeMemoStepDataProof

private theorem boolOne (b : Bool) : b.toNat = 1 ↔ b = true := by cases b <;> decide

private theorem enoughIff (V : Program 1) (valid : TermSyntaxCalibrated V) (i old a b : Nat)
    (left : evaluate rawSource (args i old) = a) (right : evaluate rawTarget (args i old) = b) :
    evaluate (enough V) (args i old) = 1 ↔ ∃ f g, guardedAuxChildren a b = some (f,g) ∧
      pair f g < i+1 ∧ evaluate lookup ((i-pair f g) ::ᵥ old ::ᵥ nil) = 1 := by
  simp only [enough,conjunctionOne,unaryValue,left,right,valid,boolOne,frameOne i old a b left right]
  constructor
  · rintro ⟨⟨f,g,frame⟩,validA,validB,earlier,accepted⟩
    have reports := childReports i old a b f g left right frame
    exact ⟨f,g,(auxChoice a b f g).mpr ⟨validA,validB,frame⟩,reports.1.mp earlier,
      reports.2.symm.trans accepted⟩
  · rintro ⟨f,g,found,earlier,accepted⟩
    obtain ⟨validA,validB,frame⟩ := (auxChoice a b f g).mp found
    have reports := childReports i old a b f g left right frame
    exact ⟨⟨f,g,frame⟩,validA,validB,reports.1.mpr earlier,reports.2.trans accepted⟩

private theorem enoughBit (V : Program 1) (i old : Nat) :
    evaluate (enough V) (args i old) = 0 ∨ evaluate (enough V) (args i old) = 1 := by
  unfold enough
  exact conjunctionBit _ _ _

theorem exact_PhysicalAuxMemoStep : ExactPhysicalAuxMemoStep := by
  intro base V valid i old
  change evaluate (step base V) (args i old) = stepValue base i old
  rw [step,evalBranch]
  cases decoded : decode (i+1) with
  | none =>
    have missing := missingKey i old decoded
    simp [stepValue,decoded,missing] <;> rfl
  | some p =>
    obtain ⟨a,b⟩ := p
    have reports := foundKey i old a b decoded
    rw [reports.1,if_neg (by decide),evalBranch,binaryValue,reports.2.1,reports.2.2]
    have meaning := enoughIff V valid i old a b reports.2.1 reports.2.2
    rcases enoughBit V i old with zero | one
    · rw [zero,if_pos rfl]
      cases pick : guardedAuxChildren a b with
      | none => simp [stepValue,decoded,pick]
      | some q =>
        obtain ⟨f,g⟩ := q
        have reject : ¬ (pair f g < i+1 ∧ evaluate lookup ((i-pair f g) ::ᵥ old ::ᵥ nil) = 1) := by
          intro pass
          have contradiction := meaning.mpr ⟨f,g,pick,pass⟩
          rw [zero] at contradiction
          cases contradiction
        simp [stepValue,decoded,pick,reject]
    · rw [one,if_neg (by decide)]
      obtain ⟨f,g,pick,earlier,hit⟩ := meaning.mp one
      simp [stepValue,decoded,pick,earlier,hit] <;> rfl

theorem exact_PhysicalAuxMemoExchange : ExactPhysicalAuxMemoExchange := by
  intro s base V baseCal syntaxCal
  exact exact_AuxExchangeMemoCalibration s base (step base V) baseCal
    (exact_PhysicalAuxMemoStep base V syntaxCal)

#print axioms exact_PhysicalAuxMemoStep
#print axioms exact_PhysicalAuxMemoExchange

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepChecks
