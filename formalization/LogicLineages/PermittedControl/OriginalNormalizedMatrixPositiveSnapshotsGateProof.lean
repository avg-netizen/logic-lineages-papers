module
public import LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshotsTargets
import LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshotsShapeProof
import LogicLineages.PermittedControl.OriginalMatrixActualReadTapeProof
import LogicLineages.PermittedControl.AffineCollapseGuardRowsProof
import LogicLineages.PermittedControl.OriginalFieldGateMatrixRowProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshots
open OrdinalComparison
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open OriginalPrintedCircuitNormalization (NormalizedGate)
open OriginalNormalizedCircuitMatrix (rows passing LimitHead typedHead baseRows basePassing limitRows limitPassing)
open SignedRowSliceValue (valueAt)
open OriginalMatrixActualReadTape (exactRowState)

private theorem equalValues (f θ : Nat → Nat) (row : Row) (x y : Int)
    (hx : valueAt f θ row.2.1 row.2.2 x) (hy : valueAt f θ row.2.1 row.2.2 y) : x = y := by
  obtain ⟨s,hs,sval⟩ := (exactRowState f θ row x).mp hx
  obtain ⟨t,ht,tval⟩ := (exactRowState f θ row y).mp hy
  have e := Option.some.inj (hs.symm.trans ht)
  subst t
  exact sval.symm.trans tval

private theorem baseShape (f θ : Nat → Nat) (g : ArbitraryHeadWireList.NormalGate)
    (snap : Snapshot) (live : actualRows f θ (OriginalNormalizedCircuitMatrix.baseRows g) snap)
    (yes : AllTrue snap) :
    snap = OriginalNormalizedCircuitMatrix.basePassing θ g := by
  cases g with
  | affine e o => exact oneEq f θ _ _ snap live yes
  | limitPair head e i o =>
      by_cases typed : LimitHead head
      · simp only [baseRows,limitRows,dif_pos typed] at live
        simp only [basePassing,limitPassing,dif_pos typed]
        let lam := typedHead head typed
        obtain ⟨a,b,c,layout,_,_,_⟩ := threeTrueShape f θ _ _ _ snap live yes
        have tru : AffineCollapseGuardRows.trueSnapshot snap := ⟨a,b,c,layout⟩
        exact ((AffineCollapseGuardRows.exactAffineCollapseGuardRows f lam typed.2 e i o θ snap).mp
          ⟨live,tru⟩).2
      · simp only [baseRows,limitRows,dif_neg typed] at live
        simp only [basePassing,limitPassing,dif_neg typed]
        exact oneEq f θ _ _ snap live yes

private theorem identityShape (f θ : Nat → Nat) (mu : NONote) (source : Nat)
    (c : Int) (terms : List MixedSameRankResidue.WeightedOperand) (snap : Snapshot)
    (live : actualRows f θ [OriginalFieldGateMatrix.identityShapeRow mu,
      OriginalFieldGateMatrix.identityAffordRow mu source,(.equalZero,c,terms)] snap)
    (yes : AllTrue snap) :
    snap = [(0,true),((θ source : Int)-(actualOrdinalNorm mu.1.repr : Int),true),(0,true)] := by
  obtain ⟨a,b,d,layout,ha,hb,hd⟩ := threeTrueShape f θ _ _ _ snap live yes
  have aa := oneEq f θ (OriginalFieldGateMatrix.identityShapeRow mu).2.1 [] [(a,true)] ha
    (by simp [AllTrue])
  have dd := oneEq f θ c terms [(d,true)] hd (by simp [AllTrue])
  have a0 : a = 0 := congrArg (fun x : Snapshot => (x.headD (0,false)).1) aa
  have d0 : d = 0 := congrArg (fun x : Snapshot => (x.headD (0,false)).1) dd
  have bb := equalValues f θ (OriginalFieldGateMatrix.identityAffordRow mu source) b _
    hb.2.1 (OriginalFieldGateMatrix.affordableValue f θ mu source)
  rw [layout,a0,bb,d0]

theorem gateShape (f θ : Nat → Nat) (g : NormalizedGate) (snap : Snapshot)
    (live : actualRows f θ (rows g) snap) (yes : AllTrue snap) : snap = passing θ g := by
  cases g with
  | base g => exact baseShape f θ g snap live yes
  | field g =>
      cases g with
      | iterate steps s o => exact oneEq f θ _ _ snap live yes
      | entry interval s o =>
          cases interval with
          | proper lam mu => exact oneEq f θ _ _ snap live yes
          | identity mu => exact identityShape f θ mu s _ _ snap live yes
      | count interval s o =>
          cases interval with
          | proper lam mu => exact oneEq f θ _ _ snap live yes
          | identity mu => exact identityShape f θ mu s _ _ snap live yes

theorem gateTrue (θ : Nat → Nat) (g : NormalizedGate) : AllTrue (passing θ g) := by
  cases g with
  | base g =>
      cases g with
      | affine e o => simp [passing,OriginalNormalizedCircuitMatrix.basePassing,AllTrue]
      | limitPair head e i o =>
          by_cases h : OriginalNormalizedCircuitMatrix.LimitHead head <;>
            simp [passing,OriginalNormalizedCircuitMatrix.basePassing,OriginalNormalizedCircuitMatrix.limitPassing,
              h,AffineCollapseGuardedLow.originalGuardSnapshot,AllTrue]
  | field g =>
      cases g with
      | iterate steps s o => simp [passing,OriginalFieldGateMatrix.passing,AllTrue]
      | entry interval s o => cases interval <;> simp [passing,OriginalFieldGateMatrix.passing,AllTrue]
      | count interval s o => cases interval <;> simp [passing,OriginalFieldGateMatrix.passing,AllTrue]

end LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshots
