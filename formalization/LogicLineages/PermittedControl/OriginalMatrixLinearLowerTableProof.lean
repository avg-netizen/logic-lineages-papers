module
public import LogicLineages.PermittedControl.OriginalMatrixLinearLowerTableTargets
import LogicLineages.PermittedControl.PreparedParameterActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixLinearLowerTable
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open PreparedProjection (LowerOperand lowerOperandRead PreparedTableTied preparedTiedProjection)
open MixedSameRankResidue (WeightedOperand orderedReads)

theorem lowerMember (top : Nat) (rows : List Row) (r : Row) (hr : r ∈ rows)
    (t : WeightedOperand) (ht : t ∈ r.2.2) (lower : t.2.rank < top) :
    t.2 ∈ lowerTable top rows :=
  List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨r,hr,List.mem_map.mpr ⟨t,ht,rfl⟩⟩,decide_eq_true lower⟩

theorem lowerReadStable (f ρ : Nat → Nat) (top z : Nat) (op : LowerOperand)
    (lower : op.rank < top) :
    lowerOperandRead f (Function.update ρ top z) op = lowerOperandRead f ρ op := by
  have different := Nat.ne_of_lt lower
  cases op <;> simp only [LowerOperand.rank] at different <;>
    simp only [lowerOperandRead,Function.update_of_ne different]

private theorem occurrence (f θ : Nat → Nat) (rows : List Row) (snap : Snapshot)
    (actual : actualRows f θ rows snap) (row : Row) (hr : row ∈ rows)
    (t : WeightedOperand) (ht : t ∈ row.2.2) :
    ∃ v : Nat, lowerOperandRead f θ t.2 = some (some v) := by
  have one (ts : List WeightedOperand) (vs : List Nat) (h : orderedReads f θ ts vs) (inTs : t ∈ ts) :
      ∃ v : Nat, lowerOperandRead f θ t.2 = some (some v) := by
    induction ts generalizing vs with
    | nil => cases inTs
    | cons a ts ih =>
        cases vs with
        | nil => exact False.elim h
        | cons v vs =>
            rcases List.mem_cons.mp inTs with same | later
            · subst a
              exact ⟨v,h.2.1⟩
            · exact ih vs h.2.2 later
  induction rows generalizing snap with
  | nil => cases hr
  | cons a rows ih =>
      cases snap with
      | nil => exact False.elim actual
      | cons v vs =>
          rcases List.mem_cons.mp hr with same | later
          · subst a
            obtain ⟨values,reads,_⟩ := actual.2.1
            exact one row.2.2 values reads ht
          · exact ih vs actual.2.2.2 later

theorem exactLinearLowerTable : ExactLinearLowerTable := by
  intro f ρ top rows
  let ops := lowerTable top rows
  have lower (op : LowerOperand) (member : op ∈ ops) : op.rank < top :=
    decide_eq_true_eq.mp (List.mem_filter.mp member).2
  have tied (live : Live f ρ ops) : PreparedTableTied f top ρ ops (assignment f ρ ops) := by
    intro j hj
    let op := ops[j]
    have used : op ∈ ops := List.getElem_mem hj
    obtain ⟨v,hit⟩ := live op used
    have chosen : assignment f ρ ops (j+1) = v := by
      change ((ops[j]?).bind (fun u => (lowerOperandRead f ρ u).join)).getD 0 = v
      rw [List.getElem?_eq_getElem hj]
      change ((some op).bind (fun u => (lowerOperandRead f ρ u).join)).getD 0 = v
      simp [hit,Option.join]
    exact ⟨lower op used,(preparedTiedProjection.1 f ρ op _).mp (chosen.symm ▸ hit)⟩
  refine ⟨lower,?_,tied,?_⟩
  · constructor
    · intro live
      exact ⟨assignment f ρ ops,tied live⟩
    · rintro ⟨ν,fit⟩ op member
      obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp member
      have h := (fit j hj).2
      change PreparedProjection.LowerOperandActual f ρ ops[j] (ν (j+1)) at h
      rw [eq] at h
      exact ⟨ν (j+1),(preparedTiedProjection.1 f ρ op _).mpr h⟩
  · intro z snap actual op member
    have original := (List.mem_filter.mp member).1
    obtain ⟨row,hr,values⟩ := List.mem_flatMap.mp original
    obtain ⟨t,ht,eq⟩ := List.mem_map.mp values
    obtain ⟨v,hit⟩ := occurrence f (Function.update ρ top z) rows snap actual row hr t ht
    rw [eq,lowerReadStable f ρ top z op (lower op member)] at hit
    exact ⟨v,hit⟩

end LogicLineages.PermittedControl.OriginalMatrixLinearLowerTable
