module
public import LogicLineages.PermittedControl.HeterogeneousSignedMatrixSliceTargets
import LogicLineages.PermittedControl.SignedRowCoordinateSliceStatementChecks
import LogicLineages.PermittedControl.SignedRowGuardedTestStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.HeterogeneousSignedMatrixSlice
open PreparedProjection
open MixedSameRankResidue (WeightedOperand)
open SignedRowCoordinateSlice (Result slice)
open SignedRowGuardedTest (Test)
open StatementChecks (fixed_signedRowCoordinateSliceHitExact fixed_signedRowValueWithoutHit)

private theorem hitCons {test : Test} {status : Result LowerOperand} {statuses : List RowResult}
    {residual : List Row} (hits : HitRows ((test,status) :: statuses) residual) :
    ∃ (b : Int) (terms : List WeightedOperand) (tail : List Row),
      status = some (some (b,terms)) ∧ residual = (test,b,terms) :: tail ∧ HitRows statuses tail := by
  cases hits with
  | cons tailHits => exact ⟨_,_,_,rfl,rfl,tailHits⟩

theorem residualRowsExact : ResidualRowsExact := by
  intro f rank a rows residual hits
  induction rows generalizing residual with
  | nil =>
    cases hits
    exact ⟨rfl,rfl⟩
  | cons r rows ih =>
    change HitRows ((r.1,slice f rank a r.2.1 r.2.2) :: sliceRows f rank a rows) residual at hits
    obtain ⟨b,terms,tail,hit,shape,tailHits⟩ := hitCons hits
    subst residual
    obtain ⟨sameTests,sameTerms⟩ := ih tail tailHits
    have remaining := (fixed_signedRowCoordinateSliceHitExact f rank a r.2.1 r.2.2 b terms hit).1
    simp [sameTests,sameTerms,remaining]

theorem exactMatrixSnapshots : ExactMatrixSnapshots := by
  intro f ρ rank a rows agree
  induction rows with
  | nil =>
    intro values
    constructor
    · intro actual
      exact ⟨[],HitRows.nil,actual⟩
    · rintro ⟨residual,hits,actual⟩
      change HitRows [] residual at hits
      cases hits
      exact actual
  | cons r rows ih =>
    intro values
    constructor
    · intro actual
      cases values with
      | nil => exact False.elim actual
      | cons value values =>
        obtain ⟨admitted,read,evaluates,tailActual⟩ := actual
        obtain ⟨b,terms,hit,residualRead⟩ :=
          (fixed_signedRowValueWithoutHit f ρ rank a r.2.1 r.2.2 agree value.1).mp read
        obtain ⟨tail,tailHits,sameTail⟩ := (ih values).mp tailActual
        refine ⟨(r.1,b,terms) :: tail,?_,⟨admitted,residualRead,evaluates,sameTail⟩⟩
        change HitRows ((r.1,slice f rank a r.2.1 r.2.2) :: sliceRows f rank a rows) _
        rw [hit]
        exact HitRows.cons tailHits
    · rintro ⟨residual,hits,actual⟩
      change HitRows ((r.1,slice f rank a r.2.1 r.2.2) :: sliceRows f rank a rows) residual at hits
      obtain ⟨b,terms,tail,hit,shape,tailHits⟩ := hitCons hits
      subst residual
      cases values with
      | nil => exact False.elim actual
      | cons value values =>
        obtain ⟨admitted,residualRead,evaluates,tailActual⟩ := actual
        have read := (fixed_signedRowValueWithoutHit f ρ rank a r.2.1 r.2.2 agree value.1).mpr
          ⟨b,terms,hit,residualRead⟩
        exact ⟨admitted,read,evaluates,(ih values).mpr ⟨tail,tailHits,tailActual⟩⟩

end LogicLineages.PermittedControl.HeterogeneousSignedMatrixSlice
