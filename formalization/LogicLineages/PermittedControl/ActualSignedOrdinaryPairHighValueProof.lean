module
public import LogicLineages.PermittedControl.ActualSignedOrdinaryPairHighTargets
import LogicLineages.PermittedControl.PreparedParameterActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSignedOrdinaryPairHigh
open FieldComparison PreparedProjection
open MixedSameRankResidue (orderedReads actualSum)
open SignedRowGuardedTest (Test sourceTestAt)
open SignedRowSliceValue (valueAt)

private theorem sumPair (c : Int) (u v : Nat) :
    (0 : Int) + (c * (u : Int) + ((-c) * (v : Int) + 0)) = c * ((u : Int)-(v : Int)) := by
  rw [zero_add,add_zero,neg_mul,mul_sub,sub_eq_add_neg]

private theorem exactValues (f ρ : Nat → Nat) (F G : ValueField) (i j : Nat) (c value : Int) :
    valueAt f ρ 0 (signedTerms F G i j c) value ↔
      ∃ u v : Nat, LowerOperandActual f ρ (.ordinary i F) u ∧
        LowerOperandActual f ρ (.ordinary j G) v ∧
        c * ((u : Int)-(v : Int)) = value := by
  constructor
  · rintro ⟨xs,h,sum⟩
    rcases xs with _ | ⟨u,xs⟩
    · exact False.elim h
    rcases xs with _ | ⟨v,xs⟩
    · exact False.elim h.2.2
    cases xs with
    | nil =>
        change (0 : Int) + (c * (u : Int) + ((-c) * (v : Int) + 0)) = value at sum
        exact ⟨u,v,h.1,h.2.2.1,(sumPair c u v).symm.trans sum⟩
    | cons w xs => exact False.elim h.2.2.2.2
  · rintro ⟨u,v,first,second,eq⟩
    refine ⟨[u,v],⟨first,(preparedTiedProjection.1 f ρ _ u).mpr first,
      second,(preparedTiedProjection.1 f ρ _ v).mpr second,True.intro⟩,?_⟩
    exact (sumPair c u v).trans eq

private theorem uniqueRead (f ρ : Nat → Nat) (a : LowerOperand) (u v : Nat)
    (h : LowerOperandActual f ρ a u) (h' : LowerOperandActual f ρ a v) : u = v := by
  have h₁ := (preparedTiedProjection.1 f ρ a u).mpr h
  have h₂ := (preparedTiedProjection.1 f ρ a v).mpr h'
  exact Option.some.inj (Option.some.inj (h₁.symm.trans h₂))

private theorem criterion (k : OrderTest) (c : Int) (nz : c ≠ 0) (u v : Nat) :
    (k.test.Holds (c * ((u : Int)-(v : Int))) ↔
      if (request k c).2 then numericalComparison u v = (request k c).1
      else numericalComparison u v ≠ (request k c).1) := by
  by_cases left : u < v
  · have cmp : numericalComparison u v = 0 := by simp [numericalComparison,left]
    have d : (u : Int) - (v : Int) < 0 := by omega
    by_cases hp : 0 < c
    · have neg := mul_neg_of_pos_of_neg hp d
      have ne : c * ((u : Int)-(v : Int)) ≠ 0 := by omega
      have nle : ¬ (0 : Int) ≤ c * ((u : Int)-(v : Int)) := by omega
      have nlt : ¬ (0 : Int) < c * ((u : Int)-(v : Int)) := by omega
      cases k <;> simp [OrderTest.test,Test.Holds,request,hp,cmp,ne,nle,nlt]
    · have hn : c < 0 := by omega
      have pos := mul_pos_of_neg_of_neg hn d
      have ne : c * ((u : Int)-(v : Int)) ≠ 0 := by omega
      cases k <;> simp [OrderTest.test,Test.Holds,request,hp,cmp,ne,pos,pos.le]
  · by_cases equal : u = v
    · subst v
      have cmp : numericalComparison u u = 1 := by simp [numericalComparison]
      by_cases hp : 0 < c <;>
        cases k <;> simp [OrderTest.test,Test.Holds,request,hp,cmp]
    · have right : v < u := by omega
      have cmp : numericalComparison u v = 2 := by simp [numericalComparison,left,equal]
      have d : 0 < (u : Int) - (v : Int) := by omega
      by_cases hp : 0 < c
      · have pos := mul_pos hp d
        have ne : c * ((u : Int)-(v : Int)) ≠ 0 := by omega
        cases k <;> simp [OrderTest.test,Test.Holds,request,hp,cmp,ne,pos,pos.le]
      · have hn : c < 0 := by omega
        have neg := mul_neg_of_neg_of_pos hn d
        have ne : c * ((u : Int)-(v : Int)) ≠ 0 := by omega
        have nle : ¬ (0 : Int) ≤ c * ((u : Int)-(v : Int)) := by omega
        have nlt : ¬ (0 : Int) < c * ((u : Int)-(v : Int)) := by omega
        cases k <;> simp [OrderTest.test,Test.Holds,request,hp,cmp,ne,nle,nlt]

theorem exactSignedPairValue : ExactSignedPairValue := by
  intro f ρ F G i j u v c nz originalF originalG k positive
  have value : ∀ t : Int,
      valueAt f ρ 0 (signedTerms F G i j c) t ↔
        c * ((u : Int)-(v : Int)) = t := by
    intro t
    rw [exactValues]
    constructor
    · rintro ⟨a,b,ha,hb,ht⟩
      rw [uniqueRead f ρ _ a u ha originalF,uniqueRead f ρ _ b v hb originalG] at ht
      exact ht
    · intro ht
      exact ⟨u,v,originalF,originalG,ht⟩
  let signed := c * ((u : Int)-(v : Int))
  have guard : k.test.Admitted := by cases k <;> trivial
  have row : source f ρ F G i j c k positive ↔ k.test.atPolarity positive signed := by
    constructor
    · rintro ⟨_,t,actual,result⟩
      have eq : signed = t := (value t).mp actual
      simpa only [eq] using result
    · intro result
      exact ⟨guard,signed,(value signed).mpr rfl,result⟩
  rw [row]
  have numeric := criterion k c nz u v
  cases hk : (request k c).2 with
  | false =>
      have same : k.test.Holds signed ↔ numericalComparison u v ≠ (request k c).1 := by
        simpa [signed,hk] using numeric
      cases positive with
      | false =>
          have flipped : (¬ k.test.Holds signed) ↔ numericalComparison u v = (request k c).1 :=
            (not_congr same).trans not_not
          simpa [Test.atPolarity,wantedBit,hk] using flipped
      | true => simpa [Test.atPolarity,wantedBit,hk] using same
  | true =>
      have same : k.test.Holds signed ↔ numericalComparison u v = (request k c).1 := by
        simpa [signed,hk] using numeric
      cases positive with
      | false => simpa [Test.atPolarity,wantedBit,hk] using (not_congr same)
      | true => simpa [Test.atPolarity,wantedBit,hk] using same

theorem exactReverseSignedPair : ExactReverseSignedPair := by
  intro f ρ F G i j c k positive
  have flip (t : Int) :
      valueAt f ρ 0 (signedTerms G F j i (-c)) t ↔
        valueAt f ρ 0 (signedTerms F G i j c) t := by
    rw [exactValues,exactValues]
    have same (u v : Nat) : (-c) * ((v : Int)-(u : Int)) = c * ((u : Int)-(v : Int)) := by
      simp only [mul_sub,neg_mul,sub_eq_add_neg,neg_neg,add_comm]
    constructor
    · rintro ⟨v,u,hv,hu,eq⟩
      exact ⟨u,v,hu,hv,(same u v).symm.trans eq⟩
    · rintro ⟨u,v,hu,hv,eq⟩
      exact ⟨v,u,hv,hu,(same u v).trans eq⟩
  exact and_congr Iff.rfl (exists_congr fun t => and_congr (flip t) Iff.rfl)

end LogicLineages.PermittedControl.ActualSignedOrdinaryPairHigh
