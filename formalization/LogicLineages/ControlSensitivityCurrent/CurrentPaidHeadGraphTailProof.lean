module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphDirectFiberProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open AdmissibleSum
open RawSourceDAG (variableIndex)
open CurrentUnitElimination (WireCtx shift OpenGraph HoldsRaw)

/-- Pack an actual lower block's witnesses, one local captured zero, and the
actual finite chain into disjoint arithmetic wire intervals. -/
def chainTape (f a : Nat→Nat) (w δ t y i : Nat) : Nat :=
  if i<w+2 then a i else if i=w+2 then 0 else
    if i<argSlot w δ 0 then (f^[i-(w+3)]) t
    else if i<directWidth w δ then (f^[i-argSlot w δ 0]) t-4
    else if i=directWidth w δ then t else y

private theorem tapeLow (f a : Nat→Nat) (w δ t y i : Nat) (h : i<w+2) :
    chainTape f a w δ t y i=a i := by simp only [chainTape,h,if_true]
private theorem tapeZero (f a : Nat→Nat) (w δ t y : Nat) :
    chainTape f a w δ t y (w+2)=0 := by simp only [chainTape,lt_irrefl,if_false,↓reduceIte]
private theorem tapeU (f a : Nat→Nat) (w δ t y j : Nat) (h : j≤δ) :
    chainTape f a w δ t y (uSlot w j)=(f^[j]) t := by
  have h0 : ¬ uSlot w j<w+2 := by unfold uSlot; omega
  have h1 : uSlot w j≠w+2 := by unfold uSlot; omega
  have h2 : uSlot w j<argSlot w δ 0 := by unfold uSlot argSlot; omega
  have h3 : uSlot w j-(w+3)=j := by unfold uSlot; omega
  simp only [chainTape,h0,h1,h2,h3,if_false,if_true]
private theorem tapeArg (f a : Nat→Nat) (w δ t y j : Nat) (h : j<δ) :
    chainTape f a w δ t y (argSlot w δ j)=(f^[j]) t-4 := by
  have h0 : ¬ argSlot w δ j<w+2 := by unfold argSlot; omega
  have h1 : argSlot w δ j≠w+2 := by unfold argSlot; omega
  have h2 : ¬ argSlot w δ j<argSlot w δ 0 := by unfold argSlot; omega
  have h3 : argSlot w δ j<directWidth w δ := by unfold argSlot directWidth; omega
  have h4 : argSlot w δ j-argSlot w δ 0=j := by unfold argSlot; omega
  simp only [chainTape,h0,h1,h2,h3,h4,if_false,if_true]
private theorem tapeInput (f a : Nat→Nat) (w δ t y : Nat) :
    chainTape f a w δ t y (directWidth w δ)=t := by
  have h0 : ¬ directWidth w δ<w+2 := by unfold directWidth; omega
  have h1 : directWidth w δ≠w+2 := by unfold directWidth; omega
  have h2 : ¬ directWidth w δ<argSlot w δ 0 := by unfold directWidth argSlot; omega
  simp only [chainTape,h0,h1,h2,lt_irrefl,if_false,↓reduceIte]
private theorem tapeOutput (f a : Nat→Nat) (w δ t y : Nat) :
    chainTape f a w δ t y (directWidth w δ+1)=y := by
  have h0 : ¬ directWidth w δ+1<w+2 := by unfold directWidth; omega
  have h1 : directWidth w δ+1≠w+2 := by unfold directWidth; omega
  have h2 : ¬ directWidth w δ+1<argSlot w δ 0 := by unfold directWidth argSlot; omega
  have h3 : ¬ directWidth w δ+1<directWidth w δ := by omega
  have h4 : directWidth w δ+1≠directWidth w δ := by omega
  simp only [chainTape,h0,h1,h2,h3,h4,if_false]

/-- Given a true actual ray graph at its positive z input, fill the whole
finite arithmetic tail, retaining the local capture-to-zero equalities. -/
theorem realizeTail (p : Policy) (f : Nat→Nat) {Γ : List Ty} (r : OpenGraph (.ground::Γ))
    (δ nξ base t v : Nat) (ht : max nξ base≤t) (hz : base≤(f^[δ]) t)
    (hr : HoldsRaw p f r (rayInputs ((f^[δ]) t-base)) v) :
    ∃ w : Nat→Nat, w (directWidth r.width δ)=t ∧ w (directWidth r.width δ+1)=v+δ ∧
      TailSpec f w r.width δ nξ base
        (r.matrix.eval p f (byIndex (fun i => w (rayPlacement r.width i)))) := by
  obtain ⟨rawOut,hout,ν,hρ,hn,hm⟩ := hr
  let wr := r.width
  let z : Variable (WireCtx wr (.ground::.ground::Γ)) .ground := shift wr .here
  let a (i : Nat) := ν (slot z i)
  let w := chainTape f a wr δ t (v+δ)
  have hRay : (byIndex (fun i => w (rayPlacement wr i)) :
      Variable (WireCtx wr (.ground::.ground::Γ)) .ground→Nat) = ν := by
    funext x
    change chainTape f a wr δ t (v+δ) (rayPlacement wr (variableIndex x))=ν x
    by_cases H : variableIndex x≤wr+1
    · rw [rayPlacement,if_pos H,tapeLow _ _ _ _ _ _ (by omega)]
      change ν (slot z (variableIndex x))=ν x
      rw [slotAt]
    · rw [rayPlacement,if_neg H,tapeZero]
      obtain ⟨u,rfl⟩ := suffixAddress wr x (by omega)
      cases u with
      | here => simp only [shiftedIndex,variableIndex,Nat.add_zero] at H; omega
      | there u =>
        cases u with
        | here => simp only [shiftedIndex,variableIndex,Nat.zero_add] at H; omega
        | there u => exact (hρ (.there u)).symm
  have hz0 : w (wr+1)=(f^[δ]) t-base := by
    unfold w
    rw [tapeLow _ _ _ _ _ _ (by omega)]
    have hd : variableIndex (shift wr (.there (.here : Variable (.ground::Γ) .ground)))=wr+1 := by
      simp only [shiftedIndex,variableIndex,Nat.zero_add]
    change ν (slot z (wr+1)) = _
    rw [← hd,slotAt]
    exact hρ .here
  have hv0 : w wr=rawOut := by
    unfold w
    rw [tapeLow _ _ _ _ _ _ (by omega)]
    have hd : variableIndex z=wr := by simp only [z,shiftedIndex,variableIndex,Nat.add_zero]
    change ν (slot z wr)=rawOut
    rw [← hd,slotAt]
    exact hn
  have hwt : w (directWidth wr δ)=t := tapeInput f a wr δ t (v+δ)
  have hwy : w (directWidth wr δ+1)=v+δ := tapeOutput f a wr δ t (v+δ)
  refine ⟨w,hwt,hwy,?_⟩
  unfold TailSpec
  dsimp only
  rw [hwt,hwy,hRay,hm,hz0,hv0]
  refine ⟨ht,?_,tapeZero f a wr δ t (v+δ),?_,rfl,by omega,?_⟩
  · exact tapeU f a wr δ t (v+δ) 0 (Nat.zero_le _)
  · have hu := tapeU f a wr δ t (v+δ) δ le_rfl
    change w (uSlot wr δ)=(f^[δ]) t at hu
    rw [hu]
    omega
  · intro j hj
    change GateSpec f (chainTape f a wr δ t (v+δ) (uSlot wr j))
      (chainTape f a wr δ t (v+δ) (uSlot wr (j+1))) (chainTape f a wr δ t (v+δ) (argSlot wr δ j))
    rw [tapeU _ _ _ _ _ _ j hj.le,tapeU _ _ _ _ _ _ (j+1) (by omega),tapeArg _ _ _ _ _ _ j hj,
      Function.iterate_succ_apply']
    exact gateWitness f _

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
