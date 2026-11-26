module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportTargets
public import Mathlib.Tactic.SplitIfs

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportProof
open PolynomialGraphCompletion WordLinearDecisionCompletion OutcomeTransport
open LogicLineages.ModelsAlgebra.Forests

def asOutcome (d : OutcomeData) : Outcome := ⟨d.1,d.2⟩

theorem lookup_correct (maximum : Nat) (rows : List Row) (outcomes : List Outcome)
    (ν : Nat → Nat) (h : List.Forall₂ (fun r o => OutcomeCorrect maximum r o ν) rows outcomes) :
    ∀ r ∈ rows, OutcomeCorrect maximum r
      (asOutcome (lookup (Encodable.encode r) (makeTable rows (outcomes.map outcomeData)))) ν := by
  induction h with
  | nil => simp
  | @cons a o rows outcomes hhead htail ih =>
      intro r hr
      by_cases hk : Encodable.encode a = Encodable.encode r
      · have he : a = r := Encodable.encode_injective hk
        subst r
        simpa only [makeTable,List.zip_cons_cons,List.map_cons,lookup,if_pos rfl,if_true,
          asOutcome,outcomeData] using hhead
      · have hrest : r ∈ rows := by
          rcases List.mem_cons.mp hr with he | he
          · subst r
            exact False.elim (hk rfl)
          · exact he
        simpa only [makeTable,List.zip_cons_cons,List.map_cons,lookup,if_neg hk] using ih r hrest

theorem outcomeFormula_eval (maximum : Nat) (r : Row) (o : Outcome) (ν : Nat → Nat)
    (h : OutcomeCorrect maximum r o ν) :
    (Formula.eval ν (outcomeFormula (outcomeData o)) ↔ 0 ≤ RowValue r ν) := by
  rcases h with ⟨ht,hn⟩ | ⟨ht,hp⟩ | ⟨ht,hl,hvalue⟩
  · simp [outcomeFormula,outcomeData,ht,Formula.eval,not_le_of_gt hn]
  · simp [outcomeFormula,outcomeData,ht,Formula.eval,le_of_lt hp]
  · simp [outcomeFormula,outcomeData,ht,Formula.eval,Atom.eval,hvalue]

theorem inequalityRows_conj (p q : Formula) :
    inequalityRows (.conj p q) = inequalityRows p++inequalityRows q := by
  simp only [inequalityRows,CotreePresburgerUnit.Boolean.atoms,List.filterMap_append]

theorem inequalityRows_disj (p q : Formula) :
    inequalityRows (.disj p q) = inequalityRows p++inequalityRows q := by
  simp only [inequalityRows,CotreePresburgerUnit.Boolean.atoms,List.filterMap_append]

theorem congruences_conj (p q : Formula) :
    congruences (.conj p q) = congruences p++congruences q := by
  simp only [congruences,CotreePresburgerUnit.Boolean.atoms,List.filterMap_append]

theorem congruences_disj (p q : Formula) :
    congruences (.disj p q) = congruences p++congruences q := by
  simp only [congruences,CotreePresburgerUnit.Boolean.atoms,List.filterMap_append]

/-- The literal congruence occurrence list is unchanged even on an
inconsistent or malformed row-outcome table. -/
theorem rewriteWith_congruences (table : Table) (p : Formula) :
    congruences (rewriteWith table p) = congruences p := by
  induction p with
  | bot => rfl
  | top => rfl
  | atom a =>
      cases a with
      | nonnegative r =>
          simp only [rewriteWith]
          unfold outcomeFormula
          split_ifs <;> rfl
      | divisible m r => rfl
  | neg p ih => exact ih
  | conj p q ihp ihq => simp only [rewriteWith,congruences_conj,ihp,ihq]
  | disj p q ihp ihq => simp only [rewriteWith,congruences_disj,ihp,ihq]

private theorem rewriteWith_eval (table : Table) (ν : Nat → Nat) : ∀ p : Formula,
    (∀ r ∈ inequalityRows p,
      Formula.eval ν (outcomeFormula (lookup (Encodable.encode r) table)) ↔ 0 ≤ RowValue r ν) →
    (Formula.eval ν (rewriteWith table p) ↔ Formula.eval ν p) := by
  intro p
  induction p with
  | bot => intro h; rfl
  | top => intro h; rfl
  | atom a =>
      intro h
      cases a with
      | nonnegative r =>
          exact h r (by simp [inequalityRows,CotreePresburgerUnit.Boolean.atoms])
      | divisible m r => rfl
  | neg p ih =>
      intro h
      exact not_congr (ih h)
  | conj p q ihp ihq =>
      intro h
      apply and_congr
      · apply ihp
        intro r hr
        exact h r (by rw [inequalityRows_conj]; exact List.mem_append_left _ hr)
      · apply ihq
        intro r hr
        exact h r (by rw [inequalityRows_conj]; exact List.mem_append_right _ hr)
  | disj p q ihp ihq =>
      intro h
      apply or_congr
      · apply ihp
        intro r hr
        exact h r (by rw [inequalityRows_disj]; exact List.mem_append_left _ hr)
      · apply ihq
        intro r hr
        exact h r (by rw [inequalityRows_disj]; exact List.mem_append_right _ hr)

theorem exactCorrelatedBody : OutcomeTransportTargets.ExactCorrelatedBody := by
  constructor
  · intro maximum p outcomes ν h
    let table := makeTable (inequalityRows p) (outcomes.map outcomeData)
    change Formula.eval ν (rewriteWith table p) ↔ Formula.eval ν p
    apply rewriteWith_eval table ν p
    intro r hr
    have hc := lookup_correct maximum (inequalityRows p) outcomes ν h r hr
    exact outcomeFormula_eval maximum r (asOutcome (lookup (Encodable.encode r) table)) ν hc
  · intro p outcomes
    exact rewriteWith_congruences _ p

/- Explicit per-file audit includes private helpers before module export. -/
#print axioms lookup_correct
#print axioms outcomeFormula_eval
#print axioms inequalityRows_conj
#print axioms inequalityRows_disj
#print axioms congruences_conj
#print axioms congruences_disj
#print axioms rewriteWith_congruences
#print axioms rewriteWith_eval
#print axioms exactCorrelatedBody

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportProof
