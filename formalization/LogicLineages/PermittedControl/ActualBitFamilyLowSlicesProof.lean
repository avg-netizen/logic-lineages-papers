module
public import LogicLineages.PermittedControl.ActualBitFamilyLowSlicesTargets
import LogicLineages.PermittedControl.ActualBitFamilyLowSlicesHitProof
import LogicLineages.PermittedControl.ActualGuardedResidualBitFamilyProof
import LogicLineages.PermittedControl.OriginalMatrixLowDimensionProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyLowSlices
open OriginalPrintedTerminalBitClauses (BitRow ClauseHolds zipBits)
open ActualGuardedResidualBitFamily (Family exactZipRows)
open OriginalMatrixLowDimension (supportSet exactResidualSupportErase)
open HeterogeneousSignedMatrixSlice (Row HitRows sliceRows)

private theorem exactZipBits (rs : List Row) (bits : List Bool) (len : bits.length = rs.length) :
    wantedBits (zipBits rs bits) = bits := by
  induction rs generalizing bits with
  | nil =>
    cases bits with
    | nil => rfl
    | cons b bs => cases len
  | cons r rs ih =>
    cases bits with
    | nil => cases len
    | cons b bs =>
      change b :: wantedBits (zipBits rs bs) = b::bs
      rw [ih bs (Nat.succ.inj len)]

theorem exactBitClauseProvenance : ExactBitClauseProvenance := by
  intro f name a clause child sliced
  let rows := originalRows clause
  let values := wantedBits clause
  cases hit : extractHits (sliceRows f name a rows) with
  | none =>
    have impossible : (none : Option (List BitRow)) = some child := by
      simpa only [sliceClause,rows,hit,Option.map_none] using sliced
    cases impossible
  | some rs =>
    have trueHit := (exactOrderedHitExtraction _ _).mp hit
    have shape : zipBits rs values = child := Option.some.inj (by
      simpa only [sliceClause,rows,values,hit,Option.map_some] using sliced)
    subst child
    have len := rowsLength f name a clause rs trueHit
    have actual : originalRows (zipBits rs values) = rs := exactZipRows rs values len
    have bits := exactZipBits rs values len
    rw [actual]
    exact ⟨trueHit,bits,(exactResidualSupportErase f name a rows rs trueHit).2.2.2⟩

private theorem exactAtDigit (f ρ : Nat → Nat) (name a : Nat) (family : Family) (value : ρ name = a) :
    ActualGuardedResidualBitFamily.Holds f ρ family ↔
      ActualGuardedResidualBitFamily.Holds f ρ (sliceFamily f name a family) := by
  constructor
  · rintro ⟨clause,original,truth⟩
    obtain ⟨child,emitted,live⟩ := (exactBitClauseSlice f ρ name a clause value).mp truth
    exact ⟨child,List.mem_filterMap.mpr ⟨clause,original,emitted⟩,live⟩
  · rintro ⟨child,member,live⟩
    obtain ⟨root,source,emitted⟩ := List.mem_filterMap.mp member
    exact ⟨root,source,(exactBitClauseSlice f ρ name a root value).mpr ⟨child,emitted,live⟩⟩

theorem exactBitFamilyLowStrips : ExactBitFamilyLowStrips := by
  intro f ρ name bound family prior
  constructor
  · rintro ⟨a,below,outside,truth⟩
    let θ := Function.update ρ name a
    have atRaw : θ name = a := by simp [θ]
    exact ⟨(a,sliceFamily f name a family),List.mem_map.mpr ⟨a,List.mem_range.mpr below,rfl⟩,
      outside,(exactAtDigit f θ name a family atRaw).mp truth⟩
  · rintro ⟨branch,member,outside,truth⟩
    obtain ⟨a,below,rfl⟩ := List.mem_map.mp member
    let θ := Function.update ρ name a
    have atRaw : θ name = a := by simp [θ]
    exact ⟨a,List.mem_range.mp below,outside,(exactAtDigit f θ name a family atRaw).mpr truth⟩

theorem coordinateClause (family : Family) (k : Nat) :
    k ∈ coordinates family ↔ ∃ c ∈ family, k ∈ supportSet (originalRows c) := by
  constructor
  · intro used
    obtain ⟨row,origin,atRow⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp used)
    obtain ⟨c,member,inCase⟩ := List.mem_flatMap.mp origin
    exact ⟨c,member,List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨row,inCase,atRow⟩)⟩
  · rintro ⟨c,member,used⟩
    obtain ⟨row,origin,atRow⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp used)
    exact List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨row,List.mem_flatMap.mpr ⟨c,member,origin⟩,atRow⟩)

theorem exactBitFamilyLowDimension : ExactBitFamilyLowDimension := by
  intro f name bound family selected branch member
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp member
  have scope : coordinates (sliceFamily f name a family) ⊆ (coordinates family).erase name := by
    intro k used
    obtain ⟨child,member,atChild⟩ := (coordinateClause _ k).mp used
    obtain ⟨source,atSource,emitted⟩ := List.mem_filterMap.mp member
    have provenance := (exactBitClauseProvenance f name a source child emitted).2.2
    rw [provenance] at atChild
    have ⟨different,atOriginal⟩ := Finset.mem_erase.mp atChild
    exact Finset.mem_erase.mpr ⟨different,(coordinateClause _ k).mpr ⟨source,atSource,atOriginal⟩⟩
  exact ⟨scope,(Finset.card_le_card scope).trans_lt (Finset.card_erase_lt_of_mem selected)⟩

end LogicLineages.PermittedControl.ActualBitFamilyLowSlices
