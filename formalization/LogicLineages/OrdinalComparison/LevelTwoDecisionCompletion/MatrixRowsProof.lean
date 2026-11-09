module
public import LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.Targets

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.MatrixProof
open PolynomialGraphCompletion WordLinearDecisionCompletion LevelTwoCounterexample
open LogicLineages.ModelsAlgebra.Forests

@[simp] theorem tokens_nonnegative (r : Row) :
    Formula.tokens (.atom (.nonnegative r)) = r.2.map Prod.snd := by
  simp [Formula.tokens,CotreePresburgerUnit.Boolean.atoms,Atom.row]

@[simp] theorem tokens_negative (p : Formula) : Formula.tokens (.neg p) = p.tokens := rfl

@[simp] theorem tokens_conjunction (p q : Formula) :
    Formula.tokens (.conj p q) = p.tokens ++ q.tokens := by
  simp [Formula.tokens,CotreePresburgerUnit.Boolean.atoms,List.flatMap_append]

@[simp] theorem tokens_disjunction (p q : Formula) :
    Formula.tokens (.disj p q) = p.tokens ++ q.tokens := by
  simp [Formula.tokens,CotreePresburgerUnit.Boolean.atoms,List.flatMap_append]

@[simp] theorem meaningful_nonnegative (r : Row) (ν : Nat → Nat) :
    Formula.meaningful (.atom (.nonnegative r)) ν ↔ RowDomain r ν := by
  constructor
  · intro h s hs
    apply h s.2
    rw [tokens_nonnegative]
    exact List.mem_map.mpr ⟨s,hs,rfl⟩
  · intro h t ht
    rw [tokens_nonnegative] at ht
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
    exact h s hs

@[simp] theorem meaningful_negative (p : Formula) (ν : Nat → Nat) :
    Formula.meaningful (.neg p) ν ↔ Formula.meaningful p ν := Iff.rfl

@[simp] theorem meaningful_conjunction (p q : Formula) (ν : Nat → Nat) :
    Formula.meaningful (.conj p q) ν ↔
      Formula.meaningful p ν ∧ Formula.meaningful q ν := by
  constructor
  · intro h
    exact ⟨fun t ht => h t (by rw [tokens_conjunction]; exact List.mem_append_left _ ht),
      fun t ht => h t (by rw [tokens_conjunction]; exact List.mem_append_right _ ht)⟩
  · rintro ⟨hp,hq⟩ t ht
    rw [tokens_conjunction] at ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hp t ht
    · exact hq t ht

/-- Both sets of domains are required, regardless of the selected disjunct. -/
@[simp] theorem meaningful_disjunction (p q : Formula) (ν : Nat → Nat) :
    Formula.meaningful (.disj p q) ν ↔
      Formula.meaningful p ν ∧ Formula.meaningful q ν := by
  exact meaningful_conjunction p q ν

@[simp] theorem negate_tokens (r : Row) :
    (negateRow r).2.map Prod.snd = r.2.map Prod.snd := by
  simp [negateRow,List.map_map,Function.comp_def]

@[simp] theorem negate_domain (r : Row) (ν : Nat → Nat) :
    RowDomain (negateRow r) ν ↔ RowDomain r ν := by
  constructor
  · intro h s hs
    exact h (-s.1,s.2) (List.mem_map.mpr ⟨s,hs,rfl⟩)
  · intro h s hs
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
    exact h a ha

theorem negate_sum (xs : List (Int × Token)) (ν : Nat → Nat) :
    (xs.map (fun s => -s.1 * (wordValue s.2.2 (ν s.2.1) : Int))).sum =
      -(xs.map (fun s => s.1 * (wordValue s.2.2 (ν s.2.1) : Int))).sum := by
  induction xs with
  | nil => simp
  | cons s xs ih =>
      simp only [List.map_cons,List.sum_cons]
      rw [ih]
      simp only [neg_mul]
      omega

@[simp] theorem negate_value (r : Row) (ν : Nat → Nat) :
    RowValue (negateRow r) ν = -RowValue r ν := by
  simp only [RowValue,negateRow,List.map_map,Function.comp_def,negate_sum,neg_add]

@[simp] theorem rowEquation_meaningful (r : Row) (ν : Nat → Nat) :
    Formula.meaningful (rowEquation r) ν ↔ RowDomain r ν := by
  simp [rowEquation]

@[simp] theorem rowEquation_eval (r : Row) (ν : Nat → Nat) :
    Formula.eval ν (rowEquation r) ↔ RowValue r ν = 0 := by
  simp only [rowEquation,Formula.eval,Atom.eval,negate_value]
  omega

@[simp] theorem positiveRow_domain (i : Nat) (ν : Nat → Nat) :
    RowDomain (positiveRow i) ν := by
  simp [positiveRow,RowDomain,WordDomain]

@[simp] theorem positiveRow_value (i : Nat) (ν : Nat → Nat) :
    RowValue (positiveRow i) ν = (ν i : Int)-1 := by
  simp [positiveRow,RowValue,wordValue]
  omega

@[simp] theorem positiveRow_eval (i : Nat) (ν : Nat → Nat) :
    Formula.eval ν (.atom (.nonnegative (positiveRow i))) ↔ 0 < ν i := by
  simp only [Formula.eval,Atom.eval,positiveRow_value]
  omega

@[simp] theorem badSign_meaningful (mode : Nat) (r : Row) (ν : Nat → Nat) :
    Formula.meaningful (badSignFormula mode r) ν ↔ RowDomain r ν := by
  unfold badSignFormula
  split_ifs <;> simp

@[simp] theorem badSign_eval (mode : Nat) (r : Row) (ν : Nat → Nat) :
    Formula.eval ν (badSignFormula mode r) ↔ Pair.badSign mode (RowValue r ν) := by
  unfold badSignFormula Pair.badSign
  split_ifs <;> simp only [Formula.eval,Atom.eval,negate_value,rowEquation_eval] <;> omega

@[simp] theorem failedPositive_meaningful (flag : Bool) (ν : Nat → Nat) :
    Formula.meaningful (failedPositive flag) ν := by
  cases flag <;> simp [failedPositive,Formula.meaningful,Formula.tokens,
    CotreePresburgerUnit.Boolean.atoms]

@[simp] theorem failedPositive_eval (flag : Bool) (ν : Nat → Nat) :
    Formula.eval ν (failedPositive flag) ↔ flag = false := by
  cases flag <;> simp [failedPositive,Formula.eval]

#print axioms tokens_nonnegative
#print axioms tokens_negative
#print axioms tokens_conjunction
#print axioms tokens_disjunction
#print axioms meaningful_nonnegative
#print axioms meaningful_negative
#print axioms meaningful_conjunction
#print axioms meaningful_disjunction
#print axioms negate_tokens
#print axioms negate_domain
#print axioms negate_sum
#print axioms negate_value
#print axioms rowEquation_meaningful
#print axioms rowEquation_eval
#print axioms positiveRow_domain
#print axioms positiveRow_value
#print axioms positiveRow_eval
#print axioms badSign_meaningful
#print axioms badSign_eval
#print axioms failedPositive_meaningful
#print axioms failedPositive_eval

end LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.MatrixProof
