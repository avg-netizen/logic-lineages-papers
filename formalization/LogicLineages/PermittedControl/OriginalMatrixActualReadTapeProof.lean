module
public import LogicLineages.PermittedControl.OriginalMatrixActualReadTapeTargets
import LogicLineages.PermittedControl.PreparedParameterActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixActualReadTape
open MixedSameRankResidue (WeightedOperand orderedReads actualSum)
open PreparedProjection (lowerOperandRead preparedTiedProjection)
open ActualZeroClassReplacement (Read liftedReads readSum)
open ActualReadChargeIteration (ReadState stateValue)
open HeterogeneousSignedMatrixSlice (actualRows)
open SignedRowSliceValue (valueAt)

theorem exactReadTape : ExactReadTape := by
  intro f ρ terms reads
  induction terms generalizing reads with
  | nil =>
      cases reads <;> simp [readTape,liftedReads,orderedReads]
  | cons t terms ih =>
      cases reads with
      | nil =>
          constructor
          · intro tape
            cases h : lowerOperandRead f ρ t.2 with
            | none => simp [readTape,h] at tape
            | some q =>
                cases q with
                | none => simp [readTape,h] at tape
                | some n => cases he : readTape f ρ terms <;> simp [readTape,h,he] at tape
          · rintro ⟨h,_⟩
            cases h
      | cons rd rs =>
          constructor
          · intro tape
            cases h : lowerOperandRead f ρ t.2 with
            | none => simp [readTape,h] at tape
            | some q =>
                cases q with
                | none => simp [readTape,h] at tape
                | some n =>
                    cases he : readTape f ρ terms with
                    | none => simp [readTape,h,he] at tape
                    | some ts =>
                        have e : (t,n) :: ts = rd :: rs := by simpa [readTape,h,he] using tape
                        obtain ⟨head,tail⟩ := List.cons.inj e
                        subst rd
                        subst rs
                        obtain ⟨same,live⟩ := (ih ts).mp he
                        exact ⟨congrArg (List.cons t) same,
                          (preparedTiedProjection.1 f ρ t.2 n).mp h,h,live⟩
          · rintro ⟨same,live⟩
            obtain ⟨head,tail⟩ := List.cons.inj same
            have hit : lowerOperandRead f ρ rd.1.2 = some (some rd.2) := live.2.1
            have hits : liftedReads f ρ rs := live.2.2
            have hn : lowerOperandRead f ρ t.2 = some (some rd.2) := by
              rw [← head]
              exact hit
            have eq : (t,rd.2) = rd := Prod.ext head.symm rfl
            simp only [readTape,hn,(ih rs).mpr ⟨tail,hits⟩,Option.map_some,eq]

private theorem orderedToTape (f ρ : Nat → Nat) (terms : List WeightedOperand) (values : List Nat)
    (h : orderedReads f ρ terms values) :
    ∃ rs : List Read, rs.map Prod.fst = terms ∧ rs.map Prod.snd = values ∧ liftedReads f ρ rs := by
  induction terms generalizing values with
  | nil =>
      cases values with
      | nil => exact ⟨[],rfl,rfl,True.intro⟩
      | cons v vs => exact (False.elim h)
  | cons t ts ih =>
      cases values with
      | nil => exact (False.elim h)
      | cons v vs =>
          obtain ⟨tail,ht,hv,live⟩ := ih vs h.2.2
          exact ⟨(t,v) :: tail,congrArg (List.cons t) ht,congrArg (List.cons v) hv,
            h.1,h.2.1,live⟩

theorem exactRowState : ExactRowState := by
  intro f ρ row v
  constructor
  · rintro ⟨vs,live,eq⟩
    obtain ⟨rs,terms,values,actual⟩ := orderedToTape f ρ row.2.2 vs live
    have h := (exactReadTape f ρ row.2.2 rs).mpr ⟨terms,actual⟩
    refine ⟨⟨row.2.1,rs⟩,by simp only [readState,h,Option.map_some],?_⟩
    change row.2.1 + actualSum (rs.map Prod.fst) (rs.map Prod.snd) = v
    rw [terms,values]
    exact eq
  · rintro ⟨s,hit,eq⟩
    cases h : readTape f ρ row.2.2 with
    | none => simp [readState,h] at hit
    | some rs =>
        have orig : (⟨row.2.1,rs⟩ : ReadState) = s := by simpa [readState,h] using hit
        subst s
        obtain ⟨terms,actual⟩ := (exactReadTape f ρ row.2.2 rs).mp h
        change orderedReads f ρ (rs.map Prod.fst) (rs.map Prod.snd) at actual
        change row.2.1 + actualSum (rs.map Prod.fst) (rs.map Prod.snd) = v at eq
        rw [terms] at actual eq
        exact ⟨_,actual,eq⟩

theorem exactGuardedMatrixTapes : ExactGuardedMatrixTapes := by
  intro f ρ rows snap
  induction rows generalizing snap with
  | nil =>
      cases snap with
      | nil =>
          exact ⟨fun _ => ⟨[],True.intro⟩,fun _ => True.intro⟩
      | cons v vs =>
          constructor
          · intro bad
            exact False.elim bad
          · rintro ⟨ss,bad⟩
            cases ss <;> exact bad
  | cons row rows ih =>
      cases snap with
      | nil =>
          constructor
          · intro bad
            exact False.elim bad
          · rintro ⟨ss,bad⟩
            cases ss <;> exact bad
      | cons v vs =>
          constructor
          · rintro ⟨guard,value,pol,rs⟩
            obtain ⟨s,h,e⟩ := (exactRowState f ρ row v.1).mp value
            obtain ⟨ss,hs⟩ := (ih vs).mp rs
            exact ⟨s :: ss,guard,h,e,pol,hs⟩
          · rintro ⟨ss,h⟩
            cases ss with
            | nil => exact False.elim h
            | cons s ss =>
                obtain ⟨guard,h,e,pol,hs⟩ := h
                exact ⟨guard,(exactRowState f ρ row v.1).mpr ⟨s,h,e⟩,pol,(ih vs).mpr ⟨ss,hs⟩⟩

end LogicLineages.PermittedControl.OriginalMatrixActualReadTape
