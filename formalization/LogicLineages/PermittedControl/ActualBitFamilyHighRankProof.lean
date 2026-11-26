module
public import LogicLineages.PermittedControl.ActualBitFamilyHighTargets
import LogicLineages.PermittedControl.OriginalMatrixDenseRanksProof
import LogicLineages.PermittedControl.ActualBitFamilyLowSlicesProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesEnumerateProof
import LogicLineages.PermittedControl.ActualRankChartPrototypeReadProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyHigh
open ActualGuardedResidualBitFamily (Family Holds)
open ActualBitFamilyLowSlices (coordinates coordinateClause originalRows)
open OriginalMatrixLowDimension (supportSet)
open HeterogeneousSignedMatrixSlice (Row actualRows)
open OriginalMatrixDenseRanks (support renameRow renameTerm exactRenamedMatrix)
open OriginalPrintedTerminalBitClauses (BitRow RowHolds ClauseHolds)
open ActualFiniteOrderBranches (Pattern rename exactPatternEnumeration)
open ActualRankChartPrototype (Consistent consistentRename)
open MixedSameRankResidue (WeightedOperand)

theorem exactValidGenericCharts : ExactValidGenericCharts := by
  intro family p
  simp only [charts,List.mem_filter,decide_eq_true_eq,ValidChart]

theorem sourceCoordinate (family : Family) (clause : List BitRow) (member : clause ∈ family)
    (row : BitRow) (used : row ∈ clause) (t : WeightedOperand) (occurs : t ∈ row.1.2.2) :
    t.2.rank ∈ coordinates family :=
  (coordinateClause family t.2.rank).mpr ⟨clause,member,List.mem_toFinset.mpr
    (List.mem_flatMap.mpr ⟨row.1,List.mem_map.mpr ⟨row,used,rfl⟩,List.mem_map.mpr ⟨t,occurs,rfl⟩⟩)⟩

theorem renameWithin (family : Family) (p : Pattern) (good : ValidChart family p)
    (k : Nat) (used : k ∈ coordinates family) : rename p k < p.1 := by
  obtain ⟨_,keys,bounds,_⟩ := (exactPatternEnumeration (names family) p).mp good.1
  have name : k ∈ names family := Finset.mem_toList.mpr used
  rw [← keys] at name
  obtain ⟨e,member,rfl⟩ := List.mem_map.mp name
  rw [consistentRename p good.2.2 e member]
  exact bounds e member

private theorem rowTransport (f θ σ : Nat → Nat) (p : Pattern) (r : BitRow)
    (tie : ∀ n ∈ support [r.1], σ (rename p n) = θ n) :
    RowHolds f θ r ↔ RowHolds f σ (renameBit p r) := by
  have raw (v : Int) :
      actualRows f σ [renameRow (rename p) r.1] [(v,r.2)] ↔ actualRows f θ [r.1] [(v,r.2)] :=
    exactRenamedMatrix f θ σ (rename p) [r.1] tie [(v,r.2)]
  constructor
  · rintro ⟨admitted,v,value,bit⟩
    have c := (raw v).mpr ⟨admitted,value,bit,True.intro⟩
    exact ⟨c.1,v,c.2.1,c.2.2.1⟩
  · rintro ⟨admitted,v,value,bit⟩
    have c := (raw v).mp ⟨admitted,value,bit,True.intro⟩
    exact ⟨c.1,v,c.2.1,c.2.2.1⟩

theorem exactGenericRankTransport : ExactGenericRankTransport := by
  intro f θ σ family p covered
  have row (clause : List BitRow) (member : clause ∈ family) (r : BitRow) (used : r ∈ clause) :
      RowHolds f θ r ↔ RowHolds f σ (renameBit p r) := by
    apply rowTransport f θ σ p r
    intro n original
    obtain ⟨r',only,atRow⟩ := List.mem_flatMap.mp original
    have same := List.mem_singleton.mp only
    subst r'
    obtain ⟨t,occurs,rfl⟩ := List.mem_map.mp atRow
    exact covered _ (sourceCoordinate family clause member r used t occurs)
  constructor
  · rintro ⟨clause,member,truth⟩
    refine ⟨clause.map (renameBit p),List.mem_map.mpr ⟨clause,member,rfl⟩,?_⟩
    intro out used
    obtain ⟨r,literal,rfl⟩ := List.mem_map.mp used
    exact (row clause member r literal).mp (truth r literal)
  · rintro ⟨out,atOut,truth⟩
    obtain ⟨clause,member,rfl⟩ := List.mem_map.mp atOut
    exact ⟨clause,member,fun r used => (row clause member r used).mpr
      (truth (renameBit p r) (List.mem_map.mpr ⟨r,used,rfl⟩))⟩

theorem rankedScope (family : Family) (p : Pattern) (good : ValidChart family p) :
    ∀ clause ∈ ranked p family, ∀ r ∈ clause, ∀ t ∈ r.1.2.2, t.2.rank < p.1 := by
  intro clause used r inRow t inTerm
  obtain ⟨source,atSource,rfl⟩ := List.mem_map.mp used
  obtain ⟨row,atRow,rfl⟩ := List.mem_map.mp inRow
  obtain ⟨raw,atRaw,rfl⟩ := List.mem_map.mp inTerm
  have bound := renameWithin family p good raw.2.rank (sourceCoordinate family source atSource row atRow raw atRaw)
  rcases raw with ⟨w,op⟩
  cases op <;> exact bound

end LogicLineages.PermittedControl.ActualBitFamilyHigh
