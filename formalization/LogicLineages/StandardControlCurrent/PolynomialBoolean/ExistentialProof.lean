module
public import LogicLineages.StandardControlCurrent.PolynomialBoolean.RealizationProof
public import LogicLineages.StandardControlCurrent.PolynomialBoolean.DomainsProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolynomialBoolean.ExistentialProof
open OrdinalComparison PolynomialGraphCompletion WordLinearDecisionCompletion SemanticBasics

theorem graph_rows (d : Nat) (p : Source) (hv : p.Valid d) (ν : Nat → Nat) :
    Formula.eval ν (graphFormula (compile d p).2.1) ↔ RowsHold (compile d p).2.1 ν := by
  rw [graph_eval]
  have hf := HeadStatementChecks.finite_family_degree p.heads (DomainsProof.valid_heads d p hv)
  have hd := DomainsProof.compiled_rows d p.degree d p hv hf.2
  constructor
  · intro h r hr
    exact ⟨(hd r hr).2 ν,h r hr⟩
  · intro h r hr
    exact (h r hr).2

theorem matrix_eval (d : Nat) (p : Source) (hv : p.Valid d) (c : Bool) (ν : Nat → Nat) :
    Formula.eval ν (matrix d p c) ↔
      Positive d ν ∧ RowsHold (compile d p).2.1 ν ∧
        (if c then ¬p.eval ν else p.eval ν) := by
  simp only [matrix,Formula.eval,positive_eval,graph_rows d p hv]
  constructor
  · rintro ⟨hp,hg,ho⟩
    refine ⟨hp,hg,?_⟩
    have hs := globalSoundness d d p hv le_rfl ν hg
    cases c
    · exact hs.mp ho
    · exact fun h => ho (hs.mpr h)
  · rintro ⟨hp,hg,ho⟩
    refine ⟨hp,hg,?_⟩
    have hs := globalSoundness d d p hv le_rfl ν hg
    cases c
    · exact hs.mpr ho
    · exact fun h => ho (hs.mp h)

theorem existential (d : Nat) (p : Source) (hv : p.Valid d) (c : Bool) :
    (∃ ν, Formula.meaningful (matrix d p c) ν ∧ Formula.eval ν (matrix d p c)) ↔
      ∃ ρ, Positive d ρ ∧ (if c then ¬p.eval ρ else p.eval ρ) := by
  constructor
  · rintro ⟨ν,_,he⟩
    have h := (matrix_eval d p hv c ν).mp he
    exact ⟨ν,h.1,h.2.2⟩
  · rintro ⟨ρ,hpos,hsource⟩
    obtain ⟨ν,hframe,hgraph,_⟩ := RealizationProof.full d d p hv le_rfl ρ
    have hsourceEq := source_congr d p hv ν ρ (fun i hi => hframe i (Or.inl hi))
    refine ⟨ν,(DomainsProof.full d p hv).2 c |>.2 ν,?_⟩
    apply (matrix_eval d p hv c ν).mpr
    refine ⟨?_,hgraph,?_⟩
    · intro i hi
      rw [hframe i (Or.inl hi)]
      exact hpos i hi
    · cases c
      · exact hsourceEq.mpr hsource
      · exact fun h => hsource (hsourceEq.mp h)

theorem full : Targets.ExistentialCalibration := by
  intro d p hv
  exact ⟨existential d p hv false,existential d p hv true⟩

end LogicLineages.StandardControlCurrent.PolynomialBoolean.ExistentialProof
