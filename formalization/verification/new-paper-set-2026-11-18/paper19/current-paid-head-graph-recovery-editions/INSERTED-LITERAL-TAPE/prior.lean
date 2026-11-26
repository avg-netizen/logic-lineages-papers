module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphInsertedFiberProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
open LogicLineages.OrdinalComparison.Source
open RawSourceDAG (variableIndex)
open CurrentUnitElimination (WireCtx shift OpenGraph HoldsRaw)

private theorem bLocal (wb wc wg j : Nat) (hj : j<wb) : placeB wb wc wg j=j := by
  simp only [placeB,hj,if_true]
private theorem cLocal (wb wc wg j : Nat) (hj : j<wc) : placeC wb wc wg j=wb+j := by
  simp only [placeC,hj,if_true]
private theorem gLocal (wb wc wg j : Nat) (hj : j<wg) : placeGraph wb wc wg j=wb+wc+j := by
  simp only [placeGraph,hj,if_true]
private theorem bResult (wb wc wg : Nat) : placeB wb wc wg wb=operandEnd wb wc wg := by
  simp only [placeB,lt_irrefl,if_false,↓reduceIte]
private theorem cResult (wb wc wg : Nat) : placeC wb wc wg wc=operandEnd wb wc wg+1 := by
  simp only [placeC,lt_irrefl,if_false,↓reduceIte]
private theorem bOld (wb wc wg j : Nat) : placeB wb wc wg (wb+j+1)=insertedWidth wb wc wg+(j+1) := by
  have h0 : ¬ wb+j+1<wb := by omega
  have h1 : wb+j+1≠wb := by omega
  simp only [placeB,h0,h1,if_false]
  omega
private theorem cOld (wb wc wg j : Nat) : placeC wb wc wg (wc+j+1)=insertedWidth wb wc wg+(j+1) := by
  have h0 : ¬ wc+j+1<wc := by omega
  have h1 : wc+j+1≠wc := by omega
  simp only [placeC,h0,h1,if_false]
  omega
private theorem gInput (wb wc wg : Nat) : placeGraph wb wc wg wg=operandEnd wb wc wg+2 := by
  simp only [placeGraph,operandEnd,lt_irrefl,if_false]
private theorem gOutput (wb wc wg : Nat) : placeGraph wb wc wg (wg+1)=insertedWidth wb wc wg := by
  have h : ¬ wg+1<wg := by omega
  simp only [placeGraph,operandEnd,insertedWidth,h,if_false]
  omega

/-- Numeric witness concatenation with ONE shared original suffix. Only the
two encoded scalar summaries and the numerical input t are new addresses. -/
private def spliceTape (b c g old : Nat→Nat) (wb wc wg vb vc t j : Nat) : Nat :=
  let e := operandEnd wb wc wg
  if j<wb then b j else if j<wb+wc then c (j-wb) else if j<e then g (j-(wb+wc))
  else if j=e then vb else if j=e+1 then vc else if j=e+2 then t
  else old (j-insertedWidth wb wc wg)

private theorem tapeB (b c g old : Nat→Nat) (wb wc wg vb vc t i : Nat) (h : i<wb) :
    spliceTape b c g old wb wc wg vb vc t i=b i := by simp only [spliceTape,h,if_true]
private theorem tapeC (b c g old : Nat→Nat) (wb wc wg vb vc t i : Nat) (h : i<wc) :
    spliceTape b c g old wb wc wg vb vc t (wb+i)=c i := by
  simp only [spliceTape,show ¬ wb+i<wb by omega,show wb+i<wb+wc by omega,if_false,if_true,Nat.add_sub_cancel_left]
private theorem tapeG (b c g old : Nat→Nat) (wb wc wg vb vc t i : Nat) (h : i<wg) :
    spliceTape b c g old wb wc wg vb vc t (wb+wc+i)=g i := by
  simp only [spliceTape,operandEnd,show ¬ wb+wc+i<wb by omega,show ¬ wb+wc+i<wb+wc by omega,
    show wb+wc+i<wb+wc+wg by omega,if_false,if_true,Nat.add_sub_cancel_left]
private theorem tapeNew (b c g old : Nat→Nat) (wb wc wg vb vc t : Nat) :
    let e := operandEnd wb wc wg
    let w := spliceTape b c g old wb wc wg vb vc t
    w e=vb ∧ w (e+1)=vc ∧ w (e+2)=t := by
  dsimp only
  unfold spliceTape operandEnd
  repeat' apply And.intro
  all_goals
    repeat' first | split | rfl | omega
private theorem tapeOld (b c g old : Nat→Nat) (wb wc wg vb vc t i : Nat) :
    spliceTape b c g old wb wc wg vb vc t (insertedWidth wb wc wg+i)=old i := by
  unfold spliceTape insertedWidth operandEnd
  repeat' first | split | rfl | omega
  congr 1
  omega

private theorem insertedSound (p : LogicLineages.OrdinalComparison.Source.AdmissibleSum.Policy) (f : Nat→Nat)
    {Γ : List Ty} (hg : ∀ σ ∈ Γ, σ = .ground) (nξ level : Nat) (b c : OpenGraph Γ)
    (g : Presented DirectCtx) (ρ : Variable Γ .ground→Nat) (y : Nat)
    (h : (inserted hg nξ level b c g).holds p f (resultValues ρ y)) :
    ∃ (B₀ C₀ : Nat), HoldsRaw p f b ρ B₀ ∧ HoldsRaw p f c ρ C₀ ∧
      g.holds p f (endValues (nξ+B₀+C₀+level) y) := by
  obtain ⟨w,hρ,hb,hc,hsplice,hg'⟩ := (insertedFiber p f hg nξ level b c g ρ y).mp h
  let e := operandEnd b.width c.width g.width
  let n := insertedWidth b.width c.width g.width
  let B₀ := w e+1
  let C₀ := w (e+1)+1
  refine ⟨B₀,C₀,⟨w e,rfl,byIndex (fun j => w (placeB b.width c.width g.width j)),?_,?_,hb⟩,
    ⟨w (e+1),rfl,byIndex (fun j => w (placeC b.width c.width g.width j)),?_,?_,hc⟩,?_⟩
  · intro x
    change w (placeB b.width c.width g.width (variableIndex (shift b.width (.there x))))=ρ x
    rw [shiftedIndex,variableIndex]
    rw [show b.width+(variableIndex x+1)=b.width+variableIndex x+1 by omega,bOld]
    exact hρ (.there x)
  · change w (placeB b.width c.width g.width (variableIndex (shift b.width .here)))=w e
    rw [shiftedIndex]
    simp only [variableIndex,Nat.add_zero,bResult,e]
  · intro x
    change w (placeC b.width c.width g.width (variableIndex (shift c.width (.there x))))=ρ x
    rw [shiftedIndex,variableIndex]
    rw [show c.width+(variableIndex x+1)=c.width+variableIndex x+1 by omega,cOld]
    exact hρ (.there x)
  · change w (placeC b.width c.width g.width (variableIndex (shift c.width .here)))=w (e+1)
    rw [shiftedIndex]
    simp only [variableIndex,Nat.add_zero,cResult,e]
  · refine ⟨byIndex (fun j => w (placeGraph b.width c.width g.width j)),?_,hg'⟩
    intro x
    cases x with
    | here =>
      change w (placeGraph b.width c.width g.width (variableIndex (shift g.width .here))) = nξ+B₀+C₀+level
      simp only [shiftedIndex,variableIndex,Nat.add_zero,gInput]
      change w (e+2) = nξ+B₀+C₀+level
      unfold B₀ C₀
      omega
    | there x =>
      cases x with
      | here =>
        change w (placeGraph b.width c.width g.width (variableIndex (shift g.width (.there .here)))) = y
        simp only [shiftedIndex,variableIndex,Nat.zero_add,gOutput]
        simpa only [variableIndex,Nat.add_zero,resultValues] using hρ .here
      | there x => nomatch x

private theorem insertedComplete (p : LogicLineages.OrdinalComparison.Source.AdmissibleSum.Policy) (f : Nat→Nat)
    {Γ : List Ty} (hg : ∀ σ ∈ Γ, σ = .ground) (nξ level : Nat) (b c : OpenGraph Γ)
    (g : Presented DirectCtx) (ρ : Variable Γ .ground→Nat) (y B₀ C₀ : Nat)
    (hb : HoldsRaw p f b ρ B₀) (hc : HoldsRaw p f c ρ C₀)
    (h : g.holds p f (endValues (nξ+B₀+C₀+level) y)) :
    (inserted hg nξ level b c g).holds p f (resultValues ρ y) := by
  obtain ⟨nb,hnb,νb,hrb,hb₀,hbM⟩ := hb
  obtain ⟨nc,hnc,νc,hrc,hc₀,hcM⟩ := hc
  obtain ⟨νg,hgg,hgM⟩ := h
  let bb := b.width
  let cc := c.width
  let gg := g.width
  let e := operandEnd bb cc gg
  let w := insertedWidth bb cc gg
  let t := nξ+B₀+C₀+level
  let rB := fun i => νb (slot (shift bb .here) i)
  let rC := fun i => νc (slot (shift cc .here) i)
  let rG := fun i => νg (slot (shift gg .here) i)
  let old := fun i => resultValues ρ y (slot .here i)
  let a := spliceTape rB rC rG old bb cc gg nb nc t
  have hnew := tapeNew rB rC rG old bb cc gg nb nc t
  have hold (i : Nat) : a (w+i)=old i := tapeOld rB rC rG old bb cc gg nb nc t i
  have B : (byIndex (fun j => a (placeB bb cc gg j)) : Variable (WireCtx bb (.ground::Γ)) .ground→Nat)=νb := by
    funext x
    change a (placeB bb cc gg (variableIndex x))=νb x
    by_cases hh : variableIndex x<bb
    · rw [bLocal _ _ _ _ hh]
      unfold a
      rw [tapeB _ _ _ _ _ _ _ _ _ _ _ hh]
      change νb (slot (shift bb .here) (variableIndex x))=νb x
      rw [slotAt]
    · obtain ⟨z,rfl⟩ := suffixAddress bb x (by omega)
      rw [shiftedIndex]
      cases z with
      | here => simpa only [variableIndex,Nat.add_zero,bResult,hb₀] using hnew.1
      | there x =>
        rw [variableIndex,show bb+(variableIndex x+1)=bb+variableIndex x+1 by omega,bOld,hold,hrb]
        change resultValues ρ y (slot .here (variableIndex (.there x : Variable (.ground::Γ) .ground))) = _
        rw [slotAt]
        rfl
  have C : (byIndex (fun j => a (placeC bb cc gg j)) : Variable (WireCtx cc (.ground::Γ)) .ground→Nat)=νc := by
    funext x
    change a (placeC bb cc gg (variableIndex x))=νc x
    by_cases hh : variableIndex x<cc
    · rw [cLocal _ _ _ _ hh]
      unfold a
      rw [tapeC _ _ _ _ _ _ _ _ _ _ _ hh]
      change νc (slot (shift cc .here) (variableIndex x))=νc x
      rw [slotAt]
    · obtain ⟨z,rfl⟩ := suffixAddress cc x (by omega)
      rw [shiftedIndex]
      cases z with
      | here => simpa only [variableIndex,Nat.add_zero,cResult,hc₀] using hnew.2.1
      | there x =>
        rw [variableIndex,show cc+(variableIndex x+1)=cc+variableIndex x+1 by omega,cOld,hold,hrc]
        change resultValues ρ y (slot .here (variableIndex (.there x : Variable (.ground::Γ) .ground))) = _
        rw [slotAt]
        rfl
  have G : (byIndex (fun j => a (placeGraph bb cc gg j)) : Variable (WireCtx gg DirectCtx) .ground→Nat)=νg := by
    funext x
    change a (placeGraph bb cc gg (variableIndex x))=νg x
    by_cases hh : variableIndex x<gg
    · rw [gLocal _ _ _ _ hh]
      unfold a
      rw [tapeG _ _ _ _ _ _ _ _ _ _ _ hh]
      change νg (slot (shift gg .here) (variableIndex x))=νg x
      rw [slotAt]
    · obtain ⟨z,rfl⟩ := suffixAddress gg x (by omega)
      rw [shiftedIndex]
      cases z with
      | here => simpa only [variableIndex,Nat.add_zero,gInput,hgg,endValues,t] using hnew.2.2
      | there z =>
        cases z with
        | here =>
          simp only [variableIndex,Nat.zero_add,gOutput,hgg,endValues]
          change a w=y
          simpa only [Nat.add_zero,old,slot,RawSourceDAG.getVariable,↓reduceDIte,Option.getD_some,resultValues]
            using hold 0
        | there z => nomatch z
  apply (insertedFiber p f hg nξ level b c g ρ y).mpr
  refine ⟨a,?_,?_,?_,?_,?_⟩
  · intro x
    change a (w+variableIndex x)=resultValues ρ y x
    rw [hold,show old (variableIndex x)=resultValues ρ y x by simp only [old,slotAt]]
  · rw [B]; exact hbM
  · rw [C]; exact hcM
  · change a (e+2)=nξ+level+2+a e+a (e+1)
    rw [hnew.1,hnew.2.1,hnew.2.2]
    unfold t
    omega
  · rw [G]; exact hgM

theorem exactInsertedTemplate : Targets.ExactInsertedTemplate := by
  intro p f Γ hg nξ level b c g ρ y
  constructor
  · exact insertedSound p f hg nξ level b c g ρ y
  · rintro ⟨B₀,C₀,hB,hC,hG⟩
    exact insertedComplete p f hg nξ level b c g ρ y B₀ C₀ hB hC hG

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
