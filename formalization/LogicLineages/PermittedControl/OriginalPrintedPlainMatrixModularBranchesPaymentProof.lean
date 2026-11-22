module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixModularBranchesTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixModularBranches
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalMatrixPaidCongruence (paidRow paidTerms)
open HeterogeneousSignedMatrixSlice (Row)
open OriginalNormalizedCircuitMatrix (rowsList rows)
open OriginalPrintedPlainMatrixInfiniteLow (matrix circuit)
open OriginalPrintedPlainMatrixOrderBranches (renamed)
open OriginalMatrixDenseRanks (renameRow renameTerm renameOperand)
open SignedRowGuardedTest (Test)

private def isOrder : Test → Bool
  | .congruence _ => false
  | _ => true

private theorem originalBaseOrder (g : ArbitraryHeadWireList.NormalGate) :
    (OriginalNormalizedCircuitMatrix.baseRows g).all (fun r => isOrder r.1) = true := by
  cases g with
  | affine e o => rfl
  | limitPair head e i o =>
      by_cases typed : OriginalNormalizedCircuitMatrix.LimitHead head
      · simp only [OriginalNormalizedCircuitMatrix.baseRows,OriginalNormalizedCircuitMatrix.limitRows,dif_pos typed] <;> rfl
      · simp only [OriginalNormalizedCircuitMatrix.baseRows,OriginalNormalizedCircuitMatrix.limitRows,dif_neg typed] <;> rfl

private theorem originalFieldsOrder (g : OriginalNaturalFieldGates.Gate) :
    (OriginalFieldGateMatrix.rows g).all (fun r => isOrder r.1) = true := by
  cases g with
  | iterate steps s o => rfl
  | entry interval s o => cases interval <;> rfl
  | count interval s o => cases interval <;> rfl

private theorem originalOrder (g : OriginalPrintedCircuitNormalization.NormalizedGate) :
    (rows g).all (fun r => isOrder r.1) = true := by
  cases g with
  | base g => exact originalBaseOrder g
  | field g => exact originalFieldsOrder g

private theorem graphRowOrder (gs : List OriginalPrintedCircuitNormalization.NormalizedGate)
    (r : Row) (member : r ∈ rowsList gs) : isOrder r.1 = true := by
  obtain ⟨g,_,onGate⟩ := List.mem_flatMap.mp member
  exact List.all_eq_true.mp (originalOrder g) r onGate

private theorem orderPays (B : Nat) (ρ rename : Nat → Nat) (r : Row) (order : isOrder r.1 = true) :
    paidRow B ρ (renameRow rename r) := by
  rcases r with ⟨test,c,ts⟩
  cases test with
  | equalZero => trivial
  | positive => trivial
  | nonnegative => trivial
  | congruence m => cases order

private theorem atomPays (B : Nat) (ρ rename : Nat → Nat) (a : NormalForm.Atom) :
    paidRow B ρ (renameRow rename (OriginalPlainTerminalMatrix.atomRow a)) := by
  cases a with
  | nonnegative r => trivial
  | divisible m r =>
      intro t ht
      change t ∈ (r.2.map (fun u => (u.1,PreparedProjection.LowerOperand.coordinate u.2.name))).map
        (renameTerm rename) at ht
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
      obtain ⟨v,_,rfl⟩ := List.mem_map.mp hu
      exact Nat.zero_le _

theorem exactInitialModularPayment : ExactInitialModularPayment := by
  intro B ρ known gates p branch row hrow
  change row ∈ (matrix known gates p).map (renameRow (ActualFiniteOrderBranches.rename branch)) at hrow
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hrow
  rcases List.mem_append.mp hr with prefixMem | suffixMem
  · exact orderPays B ρ _ r (graphRowOrder (circuit known gates p) r prefixMem)
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp suffixMem
    exact atomPays B ρ _ a

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixModularBranches
