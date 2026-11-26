module
public import LogicLineages.PermittedControl.OriginalFieldGateMatrixTargets
import LogicLineages.PermittedControl.OriginalFieldGateMatrixRowProof
import LogicLineages.PermittedControl.OriginalNaturalFieldGatesProof
import LogicLineages.PermittedControl.OriginalNaturalFieldGatesIdentityProof
import LogicLineages.PermittedControl.AffineCollapsePairListLowPrefixProof
import LogicLineages.PermittedControl.TerminalEntryScanGuardProof
import LogicLineages.OrdinalComparison.RawNotationCode

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalFieldGateMatrix
open OrdinalComparison PreparedProjection
open OriginalNaturalFieldGates (Gate Valuation IdentityDomain identityValue identityHit)
open SignedRowSliceValue (valueAt)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open SignedRowGuardedTest (Test)

private theorem rowHit (f θ : Nat → Nat) (operand : LowerOperand) (out : Nat) :
    actualRows f θ [equalityRow operand out] [(0,true)] ↔
      lowerOperandRead f θ operand = some (some (θ out)) := by
  change (True ∧ valueAt f θ 0 (equalityRow operand out).2.2 0 ∧ (0 : Int) = 0 ∧ True) ↔ _
  simpa only [true_and,and_true,eq_self] using outputEquation f θ operand out

private theorem rowZero (f θ : Nat → Nat) (out : Nat) :
    actualRows f θ [zeroRow out] [(0,true)] ↔ θ out = 0 := by
  change (True ∧ valueAt f θ 0 (zeroRow out).2.2 0 ∧ (0 : Int) = 0 ∧ True) ↔ _
  simpa only [true_and,and_true,eq_self] using zeroEquation f θ out

private theorem shapeExact (mu : NONote) :
    terminalScanGuard (rawNoteEncode mu.1,rawNoteEncode mu.1) = true ↔
      mu.1.repr = 0 ∨ Order.IsSuccLimit mu.1.repr := by
  have h := terminalEntryScanGuardExact.2 (rawNoteEncode mu.1,rawNoteEncode mu.1)
  change terminalScanGuard (rawNoteEncode mu.1,rawNoteEncode mu.1) = true ↔
    ONote.NF (rawNoteDecode (rawNoteEncode mu.1)) ∧ ONote.NF (rawNoteDecode (rawNoteEncode mu.1)) ∧
      ((rawNoteDecode (rawNoteEncode mu.1)).repr = 0 ∨
        Order.IsSuccLimit (rawNoteDecode (rawNoteEncode mu.1)).repr) at h
  rw [rawNoteDecodeEncode] at h
  exact h.trans ⟨fun h => h.2.2,fun h => ⟨mu.2,mu.2,h⟩⟩

private theorem identityThree (f θ : Nat → Nat) (mu : NONote) (source : Nat) (tail : Row) :
    actualRows f θ [identityShapeRow mu,identityAffordRow mu source,tail]
      [(0,true),((θ source : Int)-(actualOrdinalNorm mu.1.repr : Int),true),(0,true)] ↔
      IdentityDomain mu (θ source) ∧ actualRows f θ [tail] [(0,true)] := by
  let gap := (θ source : Int)-(actualOrdinalNorm mu.1.repr : Int)
  change (True ∧ valueAt f θ (identityShapeRow mu).2.1 [] 0 ∧ (0 : Int) = 0 ∧
    True ∧ valueAt f θ (identityAffordRow mu source).2.1 (identityAffordRow mu source).2.2 gap ∧
      0 ≤ gap ∧ actualRows f θ [tail] [(0,true)]) ↔ _
  constructor
  · rintro ⟨_,shape,_,_,_,aff,actual⟩
    have legal := (shapeExact mu).mp ((shapeValue f θ mu).mp shape)
    have affordable : actualOrdinalNorm mu.1.repr ≤ θ source := by
      change (0 : Int) ≤ (θ source : Int)-(actualOrdinalNorm mu.1.repr : Int) at aff
      omega
    exact ⟨⟨legal,affordable⟩,actual⟩
  · rintro ⟨⟨legal,affordable⟩,actual⟩
    refine ⟨trivial,(shapeValue f θ mu).mpr ((shapeExact mu).mpr legal),rfl,
      trivial,affordableValue f θ mu source,?_,actual⟩
    change (0 : Int) ≤ (θ source : Int)-(actualOrdinalNorm mu.1.repr : Int)
    omega

private theorem coordinatePair (f θ : Nat → Nat) (source output : Nat) :
    actualRows f θ [equalityRow (.coordinate source) output] [(0,true)] ↔
      θ output = θ source :=
  (rowHit f θ (.coordinate source) output).trans (by simp [lowerOperandRead,eq_comm])

theorem exactOriginalFieldRow : ExactOriginalFieldRow := by
  intro f θ g
  cases g with
  | iterate steps s o =>
      exact (rowHit f θ (.ordinary s (.iterate steps)) o).trans
        (OriginalNaturalFieldGates.exactOrdinarySharedGateGraph f (.iterate steps s o) θ θ).1
  | entry P s o =>
      cases P with
      | proper lam mu =>
          exact (rowHit f θ (.ordinary s (.entry 0 lam mu)) o).trans
            (OriginalNaturalFieldGates.exactOrdinarySharedGateGraph f (.entry (.proper lam mu) s o) θ θ).1
      | identity mu =>
          refine (identityThree f θ mu s (equalityRow (.coordinate s) o)).trans
            ((and_congr Iff.rfl (coordinatePair f θ s o)).trans ?_)
          constructor
          · rintro ⟨hd,hv⟩
            exact ⟨hd,(identityValue f mu (θ s) (θ o) hd).mpr hv⟩
          · rintro ⟨hd,hv⟩
            exact ⟨hd,(identityValue f mu (θ s) (θ o) hd).mp hv⟩
  | count P s o =>
      cases P with
      | proper lam mu =>
          exact (rowHit f θ (.count s lam mu) o).trans
            (OriginalNaturalFieldGates.exactOrdinarySharedGateGraph f (.count (.proper lam mu) s o) θ θ).1
      | identity mu =>
          refine (identityThree f θ mu s (zeroRow o)).trans
            ((and_congr Iff.rfl (rowZero f θ o)).trans ?_)
          constructor
          · rintro ⟨hd,hv⟩
            exact ⟨hd,(identityHit f mu (θ s) (θ o) hd).mpr hv⟩
          · rintro ⟨hd,hv⟩
            exact ⟨hd,(identityHit f mu (θ s) (θ o) hd).mp hv⟩

theorem lengthOne (θ : Valuation) (g : Gate) : (rows g).length = (passing θ g).length := by
  cases g with
  | iterate steps s o => rfl
  | entry P s o => cases P <;> rfl
  | count P s o => cases P <;> rfl

theorem exactOriginalFieldList : ExactOriginalFieldList := by
  intro f θ gates
  induction gates with
  | nil => simp [rowsList,passingList,actualRows]
  | cons g gs ih =>
      change (rows g ++ rowsList gs).length = (passing θ g ++ passingList θ gs).length ∧
        (actualRows f θ (rows g ++ rowsList gs) (passing θ g ++ passingList θ gs) ↔
          ∀ q ∈ g :: gs, q.graph f θ)
      refine ⟨?_,?_⟩
      · rw [List.length_append,List.length_append,lengthOne θ g,ih.1]
      · have split :=
          AffineCollapsePairListLow.actualRowsAppend f θ (rows g) (rowsList gs)
            (passing θ g) (passingList θ gs) (lengthOne θ g)
        rw [split,exactOriginalFieldRow f θ g,ih.2]
        constructor
        · rintro ⟨hd,ht⟩ q hq
          rcases List.mem_cons.mp hq with eq | rest
          · subst q
            exact hd
          · exact ht q rest
        · intro h
          exact ⟨h g List.mem_cons_self,fun q hq => h q (List.mem_cons_of_mem _ hq)⟩

end LogicLineages.PermittedControl.OriginalFieldGateMatrix
