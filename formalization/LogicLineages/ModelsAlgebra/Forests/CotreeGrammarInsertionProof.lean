module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarInsertionTargets
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarProductionStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarInsertion.Proof
open CotreeGrammarOpen CotreeGrammarRotation CotreeGrammarProduction CotreeGrammarFlow
open CotreeGrammarOpen.Proof CotreeGrammarRotation.Proof CotreeGrammarProduction.Proof

theorem cycleInsertOccurrence : Targets.CycleInsertOccurrence := by
  intro Q _ δ x z t u ht hu
  obtain ⟨C, w, hC⟩ := (occurrenceFactorization Q δ z u x).mp hu
  obtain ⟨D, hD⟩ := (holeFactorization Q δ x t x).mp (by rw [ht]; exact List.mem_singleton_self x)
  refine ⟨plug C (plug D w), ?_, ?_⟩
  · rw [plugCounts, plugCounts, ← hC, plugCounts]
    have hd : contextCounts D = counts t := congrArg counts hD
    rw [← hd]
    apply countExt <;> intro p <;> simp only [addCounts] <;> omega
  · apply List.perm_iff_count.mpr
    intro a
    have hd := congrArg (List.count a) ((congrArg holes hD).trans ht)
    rw [contextHolesLaw] at hd
    simp only [holes] at hd
    rw [← hC, contextHolesLaw, contextHolesLaw, contextHolesLaw]
    omega

private theorem occursLift {Q : Type} {δ : Q → Q → Q} {r q x}
    (C : Context δ r q) : ∀ t : Tree δ q, Occurs x t → Occurs x (plug C t) := by
  induction C with
  | hole => intro t h; exact h
  | left C u ih => intro t h; exact Occurs.left (ih t h)
  | right u C ih => intro t h; exact Occurs.right (ih t h)

theorem cycleInsertProduction : Targets.CycleInsertProduction := by
  intro Q _ δ x z t u r s ht hp hc
  obtain ⟨C, l, v, hC⟩ := (binaryFactorization Q δ z u r s).mp hp
  apply cycleInsertOccurrence Q δ x z t u ht
  rw [← hC]
  apply occursLift C
  rcases hc with rfl | rfl
  · exact Occurs.left (Occurs.root l)
  · exact Occurs.right (Occurs.root v)

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarInsertion.Proof
