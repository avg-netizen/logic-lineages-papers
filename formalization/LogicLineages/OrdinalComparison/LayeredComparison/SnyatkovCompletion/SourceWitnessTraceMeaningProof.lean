module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceWitnessTraceTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LeastSourceWitnessSearchProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceWitnessTraceProof
open SourceWitnessTrace

theorem originalEnvironment : SourceWitnessTraceTargets.OriginalEnvironment := by
  intro ν p
  induction p generalizing ν with
  | equal a b => intro ns; cases ns <;> simp [realizes, names, residual, updateTrace]
  | less a b => intro ns; cases ns <;> simp [realizes, names, residual, updateTrace]
  | negative p ih => intro ns; cases ns <;> simp [realizes, names, residual, updateTrace]
  | conjunction p q ihp ihq => intro ns; cases ns <;> simp [realizes, names, residual, updateTrace]
  | existsNat i p ih => intro ns; cases ns <;> simp [realizes, names, residual, updateTrace, ih]

theorem leastRealizationSound : SourceWitnessTraceTargets.LeastRealizationSound := by
  intro ν p
  induction p generalizing ν with
  | equal a b => intro ns; cases ns <;> simp [leastRealization, realizes]
  | less a b => intro ns; cases ns <;> simp [leastRealization, realizes]
  | negative p ih => intro ns; cases ns <;> simp [leastRealization, realizes]
  | conjunction p q ihp ihq => intro ns; cases ns <;> simp [leastRealization, realizes]
  | existsNat i p ih =>
      intro ns
      cases ns with
      | nil => simp [leastRealization]
      | cons n ns =>
          intro h
          exact ⟨(ih _ ns h.2).1, ⟨n, h.1.1⟩⟩

theorem least_exists (ν : Nat → Nat) (p : SourceFormula) :
    p.eval ν ↔ ∃ ns, leastRealization ν p ns := by
  classical
  induction p generalizing ν with
  | equal a b => refine ⟨fun h => ⟨[], h⟩, ?_⟩; rintro ⟨ns, h⟩; exact (leastRealizationSound _ _ _ h).2
  | less a b => refine ⟨fun h => ⟨[], h⟩, ?_⟩; rintro ⟨ns, h⟩; exact (leastRealizationSound _ _ _ h).2
  | negative p ih => refine ⟨fun h => ⟨[], h⟩, ?_⟩; rintro ⟨ns, h⟩; exact (leastRealizationSound _ _ _ h).2
  | conjunction p q ihp ihq => refine ⟨fun h => ⟨[], h⟩, ?_⟩; rintro ⟨ns, h⟩; exact (leastRealizationSound _ _ _ h).2
  | existsNat i p ih =>
      constructor
      · intro h
        have hn := Nat.find_spec h
        rcases (ih (Function.update ν i (Nat.find h))).mp hn with ⟨ns, hs⟩
        exact ⟨Nat.find h :: ns, ⟨⟨hn, fun m hm => Nat.find_min h hm⟩, hs⟩⟩
      · rintro ⟨ns, h⟩
        exact (leastRealizationSound _ _ _ h).2

private theorem bind_cons_nil (w : Option Nat) (f : Nat → Option (List Nat)) :
    (w.bind (fun n => (f n).map (fun ns => n :: ns))) ≠ some [] := by
  cases w with
  | none => simp
  | some n => cases f n <;> simp

theorem bind_cons_some (w : Option Nat) (f : Nat → Option (List Nat)) (n : Nat) (ns : List Nat) :
    (w.bind (fun m => (f m).map (fun ms => m :: ms))) = some (n :: ns) ↔ w = some n ∧ f n = some ns := by
  cases w with
  | none => simp
  | some m =>
      cases hm : f m with
      | none => by_cases hmn : m = n <;> simp_all
      | some ms => by_cases hmn : m = n <;> simp_all

theorem solve_leaf (values : List Nat) (p : SourceFormula) (hp : FiniteSearchSource.test p = true)
    (htag : p.encode % 5 ≠ 4) : solve values p.encode =
      (if FiniteSearchSource.answer values p then some [] else none) := by
  rw [solve, FiniteSearchProgramsProof.literalSyntaxCode p, if_pos hp, if_neg htag,
    FiniteSearchProgramsProof.literalAnswerCode values p]

theorem actualLeastTrace : SourceWitnessTraceTargets.ActualLeastTrace := by
  intro values p
  induction p generalizing values with
  | equal a b =>
      intro hp ns
      rw [solve_leaf values _ hp (by simp [SourceFormula.encode])]
      have ht := FiniteSearchSourceProof.actualTruth values _ hp
      cases ns <;> cases ha : FiniteSearchSource.answer values (.equal a b) <;> simp_all [leastRealization]
  | less a b =>
      intro hp ns
      rw [solve_leaf values _ hp (by simp [SourceFormula.encode, Nat.add_mod])]
      have ht := FiniteSearchSourceProof.actualTruth values _ hp
      cases ns <;> cases ha : FiniteSearchSource.answer values (.less a b) <;> simp_all [leastRealization]
  | negative p ih =>
      intro hp ns
      rw [solve_leaf values _ hp (by simp [SourceFormula.encode, Nat.add_mod])]
      have ht := FiniteSearchSourceProof.actualTruth values _ hp
      cases ns <;> cases ha : FiniteSearchSource.answer values (.negative p) <;> simp_all [leastRealization]
  | conjunction p q ihp ihq =>
      intro hp ns
      rw [solve_leaf values _ hp (by simp [SourceFormula.encode, Nat.add_mod])]
      have ht := FiniteSearchSourceProof.actualTruth values _ hp
      cases ns <;> cases ha : FiniteSearchSource.answer values (.conjunction p q) <;> simp_all [leastRealization]
  | existsNat i p ih =>
      intro hp ns
      have he : solve values (SourceFormula.existsNat i p).encode =
          (LeastSourceWitness.witness (values, i, p.encode)).bind (fun n =>
            (solve (BoundedSourcePrograms.Code.update values i n) p.encode).map (fun ns => n :: ns)) := by
        rw [solve, FiniteSearchProgramsProof.literalSyntaxCode, if_pos hp]
        simp [SourceFormula.encode, Nat.add_mod, Nat.add_div]
      rw [he]
      have hbody := LeastSourceWitnessProof.existentialBodyAdmission i p hp
      cases ns with
      | nil => exact iff_of_false (bind_cons_nil _ _) (by simp [leastRealization])
      | cons n ns =>
          rw [bind_cons_some, LeastSourceWitnessProof.actualLeastWitness values i p hp n,
            ih _ hbody ns]
          have hu : PlainParameterDecision.valuation (BoundedSourcePrograms.Code.update values i n) =
              Function.update (PlainParameterDecision.valuation values) i n := by
            funext j; exact BoundedSourceProgramsProof.exactFiniteUpdate values i n j
          rw [hu]
          rfl

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceWitnessTraceProof
