module
public import LogicLineages.ControlSensitivityCurrent.CurrentAttainmentEffectiveProof
public import LogicLineages.ControlSensitivityCurrent.CurrentAttainmentTailSyntaxProof
public import LogicLineages.ControlSensitivityCurrent.CurrentAttainmentTailSemanticProof
public import LogicLineages.ControlSensitivityCurrent.CurrentCompilerStatementChecks
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentAttainment

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open GroundEquivalence ExistentialPlan
open RawSourceDAG.InputCompiler (encodeInput)
open LogicLineages.StandardControlCurrent

theorem full : CurrentAttainmentTargets.Full := by
  refine ⟨suppliedData, completePrefix, tailSyntax, ?_⟩
  intro p hp
  refine ⟨efficient_run p hp, ?_⟩
  intro h q hmod hcount
  obtain ⟨_, n, _, l, _, _, _, _, hlimit, hoff, hhead, hray⟩ := suppliedData p h
  let code := RawSourceDAG.encode ⟨[],.arrow .ground .ground,h⟩
  let c := actualOrdinalNorm l.1.repr+n+1
  let b := bound c q
  have hc : actualOrdinalNorm l.1.repr ≤ c := by dsimp [c]; omega
  let program := if finitePrefix (rawNoteEncode l.1) q b then truthProgram else tailProgram h c q
  have hfront := completePrefix l hlimit q b
  have htail := tail_correct p h l hlimit c hc hray q hmod hcount
  have satisfiable : (∃ ρ, program.eval p Phi ρ Fin.elim0) ↔ Attains l.1.repr q := by
    by_cases hf : finitePrefix (rawNoteEncode l.1) q b = true
    · have ⟨t,_,ht⟩ := hfront.mp hf
      have htruth : ∃ ρ, truthProgram.eval p Phi ρ Fin.elim0 := ⟨fun _ => 0, rfl⟩
      simp only [program, if_pos hf]
      exact ⟨fun _ => ⟨t,ht⟩, fun _ => htruth⟩
    · simp only [program, if_neg hf]
      rw [htail]
      constructor
      · rintro ⟨t,_,ht⟩
        exact ⟨t,ht⟩
      · rintro ⟨t,ht⟩
        by_cases ht' : t < b
        · exact False.elim (hf (hfront.mpr ⟨t,ht',ht⟩))
        · exact ⟨t,Nat.le_of_not_gt ht',ht⟩
  have he : select (headCode p code) (offset p code) code q = encodeInput program := by
    change offset p code = c at hoff
    rw [hoff, hhead]
    unfold select
    change (if finitePrefix (rawNoteEncode l.1) q b then truthCode else tailCode code c q) = _
    unfold program
    by_cases hf : finitePrefix (rawNoteEncode l.1) q b = true
    · rw [if_pos hf, if_pos hf]; rfl
    · rw [if_neg hf, if_neg hf]
      exact (tailSyntax h c q).symm
  refine ⟨l, program, hhead, satisfiable, ?_, ?_⟩
  · change CurrentCompiler.compile (2, select (headCode p code) (offset p code) code q) =
      CurrentCompiler.expected program
    rw [he]
    exact (CurrentCompiler.literal_outputs.1 2 program).2
  · have hs := CurrentCompiler.StatementChecks.fixed_complete_compiler.2.2.2.2.1 Phi standard_growth p 2 program
    exact ⟨by rw [hs.1, satisfiable]; exact not_not.symm,
      by rw [hs.2, satisfiable]; exact not_not.symm⟩

end LogicLineages.ControlSensitivityCurrent.CurrentAttainment
