module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphNumericProof
public import LogicLineages.ControlSensitivityCurrent.CurrentUnitEliminationWireProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open AdmissibleSum
open RawSourceDAG (variableIndex)
open CurrentUnitElimination (WireCtx shift OpenGraph HoldsRaw groundWireCtx formulaEvalRename)

/-- Row-by-row valuation for a finite ground frame; no metavariable number
is guessed and malformed positions never enter the source proof. -/
def byIndex {Γ : List Ty} (ν : Nat → Nat) (x : Variable Γ .ground) : Nat := ν (variableIndex x)

theorem indexedPull {Γ Ξ : List Ty} (hΓ : ∀ σ ∈ Γ, σ = .ground) (hΞ : ∀ σ ∈ Ξ, σ = .ground)
    (z : Variable Ξ .ground) (place : Nat→Nat) (ν : Variable Ξ .ground→Nat) (w : Nat→Nat)
    (hw : ∀ i, i < Ξ.length → ν (slot z i)=w i)
    (hr : ∀ i, i < Γ.length → place i < Ξ.length)
    (p : Policy) (f : Nat→Nat) (m : SourceAST.Formula Γ) :
    (CurrentUnitElimination.renameFormula (route hΓ z place) m).eval p f ν =
      m.eval p f (byIndex (fun i => w (place i))) := by
  rw [formulaEvalRename]
  congr 1
  funext x
  rw [groundRoute]
  exact hw _ (hr _ (indexBound x))

theorem suffixAddress {Γ : List Ty} (w : Nat) (x : Variable (WireCtx w Γ) .ground)
    (hx : w ≤ variableIndex x) : ∃ y : Variable Γ .ground, x = shift w y := by
  induction w with
  | zero => exact ⟨x,rfl⟩
  | succ w ih =>
    cases x with
    | here => simp [variableIndex] at hx
    | there x =>
      have h : w ≤ variableIndex x := by simpa only [variableIndex,Nat.add_le_add_iff_right] using hx
      obtain ⟨y,hy⟩ := ih x h
      exact ⟨y,congrArg Variable.there hy⟩

private theorem directAddress (wr δ i : Nat) : rayPlacement wr i < directWidth wr δ+2 := by
  unfold rayPlacement directWidth
  split <;> omega

/-- Direct graph open fiber expressed in its actual numerical wire indices.
Each direction constructs the actual typed valuation or reads it back. -/
theorem directFiber (p : Policy) (f : Nat→Nat) (hf : FullAddition.Targets.SourceGrowth f)
    {Γ : List Ty} (hg : ∀ σ ∈ Γ, σ = .ground) (wrData : OpenGraph (.ground :: Γ))
    (δ nξ base : Nat) (small points : List Nat) (t y : Nat) :
    (direct hg δ nξ base small points wrData).holds p f (endValues t y) ↔
      ∃ w : Nat → Nat, w (directWidth wrData.width δ)=t ∧ w (directWidth wrData.width δ+1)=y ∧
        directBody (evalLayout f w) wrData.width δ nξ base small points
          (wrData.matrix.eval p f (byIndex (fun i => w (rayPlacement wrData.width i))))=true := by
  let r := wrData
  let n := directWidth r.width δ
  let Ξ := WireCtx n DirectCtx
  let z : Variable Ξ .ground := shift n .here
  let z' : Variable Ξ .ground := shift n (.there .here)
  let hs := groundWireCtx n DirectCtx directGround
  let hr := groundWireCtx r.width (.ground::.ground::Γ) (groundCons (groundCons hg))
  have hlen : Ξ.length=n+2 := by rw [widthLength]; rfl
  have hi : variableIndex z=n := by simp only [z,shiftedIndex,variableIndex,Nat.add_zero]
  have hi' : variableIndex z'=n+1 := by simp only [z',shiftedIndex,variableIndex,Nat.zero_add]
  have hframe : ∀ i, i < Ξ.length → rayPlacement r.width i < Ξ.length := by
    intro i _
    rw [hlen]
    exact directAddress r.width δ i
  have hcopy (ν : Variable Ξ .ground→Nat) (w : Nat→Nat) (hw : ∀ i, i < Ξ.length → ν (slot z i)=w i) :
      (direct hg δ nξ base small points r).matrix.eval p f ν =
        directBody (evalLayout f w) r.width δ nξ base small points
          (r.matrix.eval p f (byIndex (fun i => w (rayPlacement r.width i)))) := by
    let M := CurrentUnitElimination.renameFormula (route hr z (rayPlacement r.width)) r.matrix
    change (directBody (typedLayout z) r.width δ nξ base small points M).eval p f ν = _
    have hl : directWidth r.width δ+1<Ξ.length := by rw [hlen]; omega
    rw [(evalMap p f hf z ν Ξ.length w hw).wholePart _ _ _ _ hl]
    rw [show M.eval p f ν = _ from indexedPull hr hs z (rayPlacement r.width) ν w hw
      (fun i _ => by rw [hlen]; exact directAddress r.width δ i) p f r.matrix]
  constructor
  · rintro ⟨ν,he,hm⟩
    let w : Nat→Nat := fun i => ν (slot z i)
    have h0 : w n=t := by
      change ν (slot z n)=t
      rw [← hi,slotAt]
      exact he .here
    have h1 : w (n+1)=y := by
      change ν (slot z (n+1))=y
      rw [← hi',slotAt]
      exact he (.there .here)
    exact ⟨w,h0,h1,(hcopy ν w (fun _ _ => rfl)).symm.trans hm⟩
  · rintro ⟨w,ht,hy,hm⟩
    let ν : Variable Ξ .ground → Nat := byIndex w
    have hEq (i : Nat) (h : i<Ξ.length) : ν (slot z i)=w i := congrArg w (indexSlot hs z h)
    refine ⟨ν,?_,(hcopy ν w hEq).trans hm⟩
    intro x
    cases x with
    | here => change w (variableIndex z)=t; rwa [hi]
    | there x =>
      cases x with
      | here => change w (variableIndex z')=y; rwa [hi']
      | there x => nomatch x

def rayInputs {Γ : List Ty} (n : Nat) : Variable (.ground::Γ) .ground→Nat :=
  ExistentialPlan.extend (fun _ => 0) n

theorem observedRay (p : Policy) (f : Nat→Nat) {Γ : List Ty} (r : OpenGraph (.ground::Γ))
    (w : Nat→Nat) (hz : w (r.width+2)=0)
    (hm : r.matrix.eval p f (byIndex (fun i => w (rayPlacement r.width i)))=true) :
    HoldsRaw p f r (rayInputs (w (r.width+1))) (w r.width+1) := by
  refine ⟨w r.width,rfl,byIndex (fun i => w (rayPlacement r.width i)),?_,?_,hm⟩
  · intro x
    cases x with
    | here =>
      change w (rayPlacement r.width (variableIndex (shift r.width (.there .here))))=w (r.width+1)
      simp only [shiftedIndex,variableIndex,Nat.zero_add,rayPlacement,le_refl,if_pos]
    | there x =>
      change w (rayPlacement r.width (variableIndex (shift r.width (.there (.there x)))))=0
      have h : ¬ r.width+(variableIndex x+1+1) ≤ r.width+1 := by omega
      simp only [shiftedIndex,variableIndex,rayPlacement,h,if_false,hz]
  · change w (rayPlacement r.width (variableIndex (shift r.width .here)))=w r.width
    rw [shiftedIndex]
    simp [variableIndex,rayPlacement]

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
