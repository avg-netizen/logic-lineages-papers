module
public import LogicLineages.PermittedControl.OriginalNormalizedCircuitMatrixTargets
import LogicLineages.PermittedControl.OriginalNormalizedCircuitMatrixBaseProof
import LogicLineages.PermittedControl.OriginalFieldGateMatrixProof
import LogicLineages.PermittedControl.AffineCollapsePairListLowPrefixProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalNormalizedCircuitMatrix
open ArbitraryHeadSharedWire (Valuation)
open OriginalPrintedCircuitNormalization (NormalizedGate Holds)
open HeterogeneousSignedMatrixSlice (actualRows)

private theorem one (f : Nat → Nat) (θ : Valuation) (g : NormalizedGate) :
    (rows g).length = (passing θ g).length ∧
      (actualRows f θ (rows g) (passing θ g) ↔ g.graph f θ) := by
  cases g with
  | base g => exact exactNormalizedBaseRows f θ g
  | field g => exact ⟨OriginalFieldGateMatrix.lengthOne θ g,
      OriginalFieldGateMatrix.exactOriginalFieldRow f θ g⟩

theorem exactNormalizedCircuitRows : ExactNormalizedCircuitRows := by
  intro f θ gates
  induction gates with
  | nil => simp [rowsList,passingList,actualRows,Holds]
  | cons g gs ih =>
      change (rows g ++ rowsList gs).length = (passing θ g ++ passingList θ gs).length ∧
        (actualRows f θ (rows g ++ rowsList gs) (passing θ g ++ passingList θ gs) ↔
          ∀ q ∈ g :: gs, q.graph f θ)
      obtain ⟨width,head⟩ := one f θ g
      refine ⟨?_,?_⟩
      · rw [List.length_append,List.length_append,width,ih.1]
      · have split :=
          AffineCollapsePairListLow.actualRowsAppend f θ (rows g) (rowsList gs)
            (passing θ g) (passingList θ gs) width
        rw [split,head,ih.2]
        constructor
        · rintro ⟨hd,ht⟩ q hq
          rcases List.mem_cons.mp hq with eq | rest
          · subst q
            exact hd
          · exact ht q rest
        · intro h
          exact ⟨h g List.mem_cons_self,fun q hq => h q (List.mem_cons_of_mem _ hq)⟩

theorem exactPrintedNormalizedMatrix : ExactPrintedNormalizedMatrix := by
  intro f θ ext gates
  exact (exactNormalizedCircuitRows f θ _).2

end LogicLineages.PermittedControl.OriginalNormalizedCircuitMatrix
