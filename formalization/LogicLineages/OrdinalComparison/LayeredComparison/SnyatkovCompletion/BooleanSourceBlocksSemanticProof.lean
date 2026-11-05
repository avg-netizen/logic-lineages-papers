module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BooleanSourceBlocksTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BooleanSourceBlocksProof
open BooleanSourceBlocks

theorem admissible_eq (p : SourceFormula) : admissible p =
    (HomogeneousSource.admissible p || match p with
      | .negative q => admissible q
      | .conjunction q r => admissible q && admissible r
      | _ => false) := by cases p <;> rfl

theorem decide_eq (values : List Nat) (p : SourceFormula) : BooleanSourceBlocks.decide values p =
    (if HomogeneousSource.admissible p then HomogeneousSource.decide values p
      else match p with
        | .negative q => (BooleanSourceBlocks.decide values q).map Bool.not
        | .conjunction q r => combine (BooleanSourceBlocks.decide values q) (BooleanSourceBlocks.decide values r)
        | _ => none) := by cases p <;> rfl

private theorem combine_domain (a b : Option Bool) :
    (combine a b).isSome = (a.isSome && b.isSome) := by
  cases a <;> cases b <;> rfl

private theorem homogeneous_domain (values : List Nat) (p : SourceFormula)
    (h : HomogeneousSource.admissible p = true) :
    (BooleanSourceBlocks.decide values p).isSome = admissible p := by
  rw [decide_eq, if_pos h, HomogeneousSourceProof.exactDecisionDomain values p, admissible_eq, h]
  rfl

theorem exactDecisionDomain : BooleanSourceBlocksTargets.ExactDecisionDomain := by
  intro values p
  induction p with
  | equal a b => exact homogeneous_domain values _ rfl
  | less a b => exact homogeneous_domain values _ rfl
  | negative p ih =>
      by_cases h : HomogeneousSource.admissible (.negative p) = true
      · exact homogeneous_domain values _ h
      · rw [decide_eq, if_neg h, admissible_eq, Bool.eq_false_iff.mpr h]
        simpa only [Bool.false_or, Option.isSome_map] using ih
  | conjunction p q ihp ihq =>
      by_cases h : HomogeneousSource.admissible (.conjunction p q) = true
      · exact homogeneous_domain values _ h
      · rw [decide_eq, if_neg h, admissible_eq, Bool.eq_false_iff.mpr h]
        simpa only [Bool.false_or, combine_domain] using congrArg₂ Bool.and ihp ihq
  | existsNat i p ih =>
      by_cases h : HomogeneousSource.admissible (.existsNat i p) = true
      · exact homogeneous_domain values _ h
      · rw [decide_eq, if_neg h, admissible_eq, Bool.eq_false_iff.mpr h]
        rfl

theorem actualDecision : BooleanSourceBlocksTargets.ActualDecision := by
  classical
  intro values p
  induction p with
  | equal a b =>
      intro hp b'
      have h : HomogeneousSource.admissible (.equal a b) = true := rfl
      rw [decide_eq, if_pos h]
      exact HomogeneousSourceProof.actualDecision values _ h b'
  | less a b =>
      intro hp b'
      have h : HomogeneousSource.admissible (.less a b) = true := rfl
      rw [decide_eq, if_pos h]
      exact HomogeneousSourceProof.actualDecision values _ h b'
  | negative p ih =>
      intro hp b
      by_cases h : HomogeneousSource.admissible (.negative p) = true
      · rw [decide_eq, if_pos h]
        exact HomogeneousSourceProof.actualDecision values _ h b
      have hp' : admissible p = true := by
        rw [admissible_eq, Bool.eq_false_iff.mpr h] at hp
        exact hp
      rw [decide_eq, if_neg h]
      cases hx : BooleanSourceBlocks.decide values p with
      | none =>
          have hd := exactDecisionDomain values p
          simp [hx, hp'] at hd
      | some a =>
          have ha := (ih hp' a).mp hx
          cases a <;> cases b <;> simp_all [SourceFormula.eval]
  | conjunction p q ihp ihq =>
      intro hp b
      by_cases h : HomogeneousSource.admissible (.conjunction p q) = true
      · rw [decide_eq, if_pos h]
        exact HomogeneousSourceProof.actualDecision values _ h b
      have hpq : admissible p = true ∧ admissible q = true := by
        rw [admissible_eq, Bool.eq_false_iff.mpr h] at hp
        exact Bool.and_eq_true_iff.mp hp
      rw [decide_eq, if_neg h]
      cases hx : BooleanSourceBlocks.decide values p with
      | none =>
          have hd := exactDecisionDomain values p
          simp [hx, hpq.1] at hd
      | some a =>
          cases hy : BooleanSourceBlocks.decide values q with
          | none =>
              have hd := exactDecisionDomain values q
              simp [hy, hpq.2] at hd
          | some c =>
              have ha := (ihp hpq.1 a).mp hx
              have hc := (ihq hpq.2 c).mp hy
              cases a <;> cases c <;> cases b <;> simp_all [combine, SourceFormula.eval]
  | existsNat i p ih =>
      intro hp b
      have h : HomogeneousSource.admissible (.existsNat i p) = true := by
        rw [admissible_eq] at hp
        simpa only [Bool.or_false] using hp
      rw [decide_eq, if_pos h]
      exact HomogeneousSourceProof.actualDecision values _ h b

theorem fragmentBoundary : BooleanSourceBlocksTargets.FragmentBoundary := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp; rw [admissible_eq, hp]; rfl
  · intro p hp; rw [admissible_eq]; simp only [hp, Bool.or_true]
  · intro p q hp hq; rw [admissible_eq]; simp only [hp, hq, Bool.true_and, Bool.or_true]
  · intro i j p
    have he : admissible (.existsNat i (.negative (.existsNat j p))) = false := by
      rw [admissible_eq]
      rfl
    refine ⟨he, ?_⟩
    rw [admissible_eq]
    change (false || admissible (.existsNat i (.negative (.existsNat j p)))) = false
    rw [he]
    rfl

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BooleanSourceBlocksProof
