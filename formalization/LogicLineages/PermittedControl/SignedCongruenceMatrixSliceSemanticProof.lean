module
public import LogicLineages.PermittedControl.SignedCongruenceMatrixSliceTargets
import LogicLineages.PermittedControl.SignedCongruenceMatrixSliceReadProof
import LogicLineages.PermittedControl.SignedRowCoordinateSliceStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.SignedCongruenceMatrixSlice
open PreparedProjection
open MixedSameRankResidue (WeightedOperand)
open SharedRankResidueRow (SourceRow)
open SignedRowCoordinateSlice (Result slice untouched denotes)
open SignedCongruenceMatrix (actualRows)
open StatementChecks (fixed_signedRowCoordinateSliceHitExact)

private theorem hitCons {m : Nat} {status : Result LowerOperand} {statuses : List RowResult}
    {residual : List SourceRow} (hits : HitRows ((m,status) :: statuses) residual) :
    ∃ (b : Int) (terms : List WeightedOperand) (tail : List SourceRow),
      status = some (some (b,terms)) ∧ residual = (m,b,terms) :: tail ∧ HitRows statuses tail := by
  cases hits with
  | cons tailHits => exact ⟨_,_,_,rfl,rfl,tailHits⟩

theorem residualRanks : ResidualRanks := by
  intro f rank a rows residual hits
  induction rows generalizing residual with
  | nil =>
    cases hits
    intro r used
    simp at used
  | cons r rows ih =>
    change HitRows ((r.1,slice f rank a r.2.1 r.2.2) :: sliceRows f rank a rows) residual at hits
    obtain ⟨b,terms,tail,status,equal,tailHits⟩ := hitCons hits
    subst residual
    intro rr rowUsed t used
    rcases List.mem_cons.mp rowUsed with same | later
    · subst rr
      have remaining := (fixed_signedRowCoordinateSliceHitExact f rank a r.2.1 r.2.2 b terms status).1
      change t ∈ terms at used
      rw [remaining] at used
      exact of_decide_eq_true (List.mem_filter.mp used).2
    · exact ih tail tailHits rr later t used

private theorem rowSlice (f ρ : Nat → Nat) (rank a : Nat) (r : SourceRow)
    (agree : ρ rank = a) (positive : 0 < r.1) (b : Int) (terms : List WeightedOperand)
    (hit : slice f rank a r.2.1 r.2.2 = some (some (b,terms))) :
    denotes f ρ r.1 r.2.1 r.2.2 ↔ denotes f ρ r.1 b terms := by
  obtain ⟨_,_,_,meaning⟩ :=
    (fixed_signedRowCoordinateSliceHitExact f rank a r.2.1 r.2.2 b terms hit).2 ρ agree
  exact meaning r.1 positive

theorem actualJointSlice : ActualJointSlice := by
  intro f ρ rank a rows agree positive
  induction rows with
  | nil =>
    exact ⟨fun _ => ⟨[],HitRows.nil,[],True.intro⟩,fun _ => ⟨[],True.intro⟩⟩
  | cons r rows ih =>
    have positiveHead := positive r List.mem_cons_self
    have tails := ih (fun p member => positive p (List.mem_cons_of_mem _ member))
    constructor
    · rintro ⟨allValues,values⟩
      cases allValues with
      | nil => exact False.elim values
      | cons v vs =>
        obtain ⟨read,divisible,remaining⟩ := values
        obtain ⟨b,terms,hit⟩ := sliceExists f ρ rank a r.2.1 r.2.2 v read agree
        obtain ⟨newValues,newReads,newDivisibility⟩ :=
          (rowSlice f ρ rank a r agree positiveHead b terms hit).mp ⟨v,read,divisible⟩
        obtain ⟨rest,tailHits,tailValues,tailActual⟩ := tails.mp ⟨vs,remaining⟩
        refine ⟨(r.1,b,terms) :: rest,?_,newValues :: tailValues,⟨newReads,newDivisibility,tailActual⟩⟩
        change HitRows ((r.1,slice f rank a r.2.1 r.2.2) :: sliceRows f rank a rows) _
        rw [hit]
        exact HitRows.cons tailHits
    · rintro ⟨residual,hits,newValues,actual⟩
      change HitRows ((r.1,slice f rank a r.2.1 r.2.2) :: sliceRows f rank a rows) residual at hits
      obtain ⟨b,terms,tail,hit,equal,tailHits⟩ := hitCons hits
      subst residual
      cases newValues with
      | nil => exact False.elim actual
      | cons v vs =>
        obtain ⟨read,divisible,tailActual⟩ := actual
        obtain ⟨oldValue,oldRead,oldDivisibility⟩ :=
          (rowSlice f ρ rank a r agree positiveHead b terms hit).mpr ⟨v,read,divisible⟩
        obtain ⟨oldTail,oldActual⟩ := tails.mpr ⟨tail,tailHits,vs,tailActual⟩
        exact ⟨oldValue :: oldTail,⟨oldRead,oldDivisibility,oldActual⟩⟩

end LogicLineages.PermittedControl.SignedCongruenceMatrixSlice
