module
public import LogicLineages.PermittedControl.ActualBitFamilyExistentialLowTargets
import LogicLineages.PermittedControl.OriginalMatrixDenseRanksProof
import LogicLineages.PermittedControl.ActualBitFamilyLowSlicesProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyExistentialLow
open ActualGuardedResidualBitFamily (Family Holds)
open ActualBitFamilyLowSlices (coordinates coordinateClause originalRows)
open OriginalPrintedTerminalBitClauses (BitRow RowHolds ClauseHolds)
open OriginalMatrixDenseRanks (support renameRow renameTerm exactRenamedMatrix)
open MixedSameRankResidue (WeightedOperand)
open HeterogeneousSignedMatrixSlice (Row actualRows)

theorem exactClauseOperandInUnion (family : Family) (clause : List BitRow) (member : clause ∈ family)
    (row : BitRow) (used : row ∈ clause) (t : WeightedOperand) (atTerm : t ∈ row.1.2.2) :
    t.2.rank ∈ coordinates family :=
  (coordinateClause family t.2.rank).mpr ⟨clause,member,List.mem_toFinset.mpr
    (List.mem_flatMap.mpr ⟨row.1,List.mem_map.mpr ⟨row,used,rfl⟩,List.mem_map.mpr ⟨t,atTerm,rfl⟩⟩)⟩

private theorem renameId (r : Row) : renameRow id r = r := by
  have term (t : WeightedOperand) : renameTerm id t = t := by
    rcases t with ⟨coef,op⟩
    cases op <;> rfl
  rcases r with ⟨test,c,ts⟩
  have idList : ts.map (renameTerm id) = ts := by
    induction ts with
    | nil => rfl
    | cons t ts ih => simp only [List.map_cons,term,ih]
  change (test,c,ts.map (renameTerm id)) = (test,c,ts)
  rw [idList]

private theorem rowLocality (f ρ σ : Nat → Nat) (r : BitRow)
    (agree : ∀ k ∈ support [r.1], ρ k = σ k) :
    RowHolds f ρ r ↔ RowHolds f σ r := by
  have h (v : Int) : actualRows f σ [r.1] [(v,r.2)] ↔ actualRows f ρ [r.1] [(v,r.2)] := by
    have source := exactRenamedMatrix f ρ σ id [r.1] (fun k used => (agree k used).symm) [(v,r.2)]
    simpa only [List.map_cons,List.map_nil,renameId] using source
  constructor
  · rintro ⟨admitted,v,value,polarity⟩
    have x := (h v).mpr ⟨admitted,value,polarity,True.intro⟩
    exact ⟨x.1,v,x.2.1,x.2.2.1⟩
  · rintro ⟨admitted,v,value,polarity⟩
    have x := (h v).mp ⟨admitted,value,polarity,True.intro⟩
    exact ⟨x.1,v,x.2.1,x.2.2.1⟩

theorem exactBitFamilySupportLocality : ExactBitFamilySupportLocality := by
  intro f ρ σ family agree
  have same (clause : List BitRow) (member : clause ∈ family) (r : BitRow) (used : r ∈ clause) :=
    rowLocality f ρ σ r (fun k inRow => by
      obtain ⟨row,origin,atRow⟩ := List.mem_flatMap.mp inRow
      have only := List.mem_singleton.mp origin
      subst row
      obtain ⟨t,atTerm,rfl⟩ := List.mem_map.mp atRow
      exact agree _ (exactClauseOperandInUnion family clause member r used t atTerm))
  constructor
  · rintro ⟨clause,member,holds⟩
    exact ⟨clause,member,fun row used => (same clause member row used).mp (holds row used)⟩
  · rintro ⟨clause,member,holds⟩
    exact ⟨clause,member,fun row used => (same clause member row used).mpr (holds row used)⟩

end LogicLineages.PermittedControl.ActualBitFamilyExistentialLow
