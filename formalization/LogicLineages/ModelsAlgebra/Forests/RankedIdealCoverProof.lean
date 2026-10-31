module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealCoverTargets
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealCoverAssemblyStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRankStatementChecks
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealCover.Proof
open RankedParse RankedIdealRank RankedIdealComponents RankedIdealCompletion RankedIdealRegularCode RankedIdealSpineCode RankedIdealCoverAssembly RankedGraphImage
 theorem nonlinearExact : Targets.NonlinearExact := by
  intro C q
  simp only [nonlinear, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨o,_,x,_,y,_,h⟩
    exact ⟨o,x,y,h⟩
  · rintro ⟨o,x,y,h⟩
    exact ⟨o,RankedIdealSpineCode.Proof.ops_mem o,x,C.complete x,y,C.complete y,h⟩
 theorem rankPositive (C : Code) (q : C.machine.State) : 0 < rank C.machine q := by
  apply Finset.card_pos.mpr
  exact ⟨q,by simp [predecessors,RankedIdealRank.StatementChecks.reachReflexive C.machine q]⟩
 theorem rankBound (C : Code) (q : C.machine.State) : rank C.machine q ≤ Fintype.card C.machine.State :=
  Finset.card_le_univ (predecessors C.machine q)
 theorem piecesCorrect : Targets.PiecesCorrect := by
  intro C n
  induction n with
  | zero =>
      intro q hq
      have hp := rankPositive C q
      omega
  | succ n ih =>
      intro q hq
      by_cases hp : q ∈ productive C.machine
      · by_cases hn : nonlinear C q = true
        · simp only [pieces,if_pos hp,if_pos hn]
          constructor
          · intro B hB
            have he := List.mem_singleton.mp hB
            subst B
            exact RankedIdealRegularCode.StatementChecks.componentIdeal C q ((nonlinearExact C q).mp hn)
          · intro t
            constructor
            · rintro ⟨B,hB,ht⟩
              have he := List.mem_singleton.mp hB
              subst B
              exact (RankedIdealRegularCode.StatementChecks.componentExact C q t).mp ht
            · intro ht
              exact ⟨component C q,by simp,(RankedIdealRegularCode.StatementChecks.componentExact C q t).mpr ht⟩
        · have hrec : LowerCorrect C q (pieces C n) := by
            intro p hpq
            have hlt := RankedIdealRank.StatementChecks.lowerRank C.machine p q hpq
            exact ih p (by omega)
          have hlinear : ¬NonlinearAt C.machine q := fun h => hn ((nonlinearExact C q).mpr h)
          simpa only [pieces,if_pos hp,if_neg hn] using
            And.intro (RankedIdealCoverAssembly.StatementChecks.piecesIdeal C q (pieces C n) hrec)
              (RankedIdealCoverAssembly.StatementChecks.piecesExact C q (pieces C n) hrec hlinear)
      · simp only [pieces,if_neg hp]
        constructor
        · intro B hB; simp at hB
        · intro t
          constructor
          · rintro ⟨B,hB,_⟩; simp at hB
          · intro ht
            exact False.elim (hp (RankedIdealCompletion.StatementChecks.runProductive C.machine t q ht))
 theorem cover_mem (C : Code) B : B ∈ cover C ↔
    ∃ q, C.machine.accept q = true ∧ B ∈ pieces C (Fintype.card C.machine.State) q := by
  simp [cover,C.complete]
 theorem coverCorrect : Targets.CoverCorrect := by
  intro C
  constructor
  · intro B hB
    obtain ⟨q,_,hB⟩ := (cover_mem C B).mp hB
    exact (piecesCorrect C _ q (rankBound C q)).1 B hB
  · intro t
    constructor
    · rintro ⟨B,hB,ht⟩
      obtain ⟨q,hq,hB⟩ := (cover_mem C B).mp hB
      have hr := ((piecesCorrect C _ q (rankBound C q)).2 t).mp ⟨B,hB,ht⟩
      obtain ⟨u,htu,hu⟩ := (RankedIdealCompletion.StatementChecks.acceptanceExact C.machine t).mp ⟨q,hr,hq⟩
      exact ⟨u,hu,htu⟩
    · rintro ⟨u,hu,htu⟩
      obtain ⟨q,hr,hq⟩ := (RankedIdealCompletion.StatementChecks.acceptanceExact C.machine t).mpr ⟨u,htu,hu⟩
      obtain ⟨B,hB,ht⟩ := ((piecesCorrect C _ q (rankBound C q)).2 t).mpr hr
      exact ⟨B,(cover_mem C B).mpr ⟨q,hq,hB⟩,ht⟩
 theorem emptyExact : Targets.EmptyExact := by
  intro C
  constructor
  · intro he t ht
    obtain ⟨B,hB,_⟩ := ((coverCorrect C).2 t).mpr
      ⟨t,ht,RankedIdealContext.StatementChecks.embeddingReflexive t⟩
    simp [he] at hB
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro B hB
    obtain ⟨t,ht⟩ := ((coverCorrect C).1 B hB).nonempty
    obtain ⟨u,hu,_⟩ := ((coverCorrect C).2 t).mp ⟨B,hB,ht⟩
    exact h u hu
end LogicLineages.ModelsAlgebra.Forests.RankedIdealCover.Proof
