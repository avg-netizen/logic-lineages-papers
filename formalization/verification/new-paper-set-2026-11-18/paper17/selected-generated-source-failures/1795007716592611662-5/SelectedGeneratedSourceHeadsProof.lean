module
public import LogicLineages.PermittedControl.SelectedGeneratedSourceSoundProof
public import LogicLineages.PermittedControl.EncodedEvaluatorProof
public import LogicLineages.PermittedControl.SelectedGradedPositivityProof
public import LogicLineages.StandardControlCurrent.PolicySourceInterfaceProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedGeneratedSourceHeadsProof
open OrdinalComparison Source Source.ForwardTranslation SelectedGeneratedSource

theorem fixedHeads : SelectedGeneratedSourceTargets.FixedHeads := by
  intro ctrl K hctrl c
  obtain ⟨hp,hpos,hlim,he,_⟩ := StandardControlCurrent.PolicySourceInterfaceProof.heads c
  refine ⟨hp,hpos,hlim,he,?_⟩
  have ev : Targets.EffectiveEvaluation ctrl := by
    rcases SelectedGradedPositivityProof.selected_forms hctrl with rfl | ⟨b,rfl⟩
    · exact selectedClosedEvaluation.1.2
    · exact (selectedClosedEvaluation.2 b).2
  let z := scalarHeadNote c
  have hz : z.1.repr = fixedHead c := by
    change (scalarHeadNote c).1.repr = fixedHead c
    rw [scalarHeadNote, naturalProductDenotation]
    simp [fixedHead, ONote.repr]
  have hc : Computable (fun n : Nat => evaluatorWith ctrl (encodedFiniteTail (rawNoteEncode z.1) n)) :=
    ev.2.2.2.1.comp
      (encodedFiniteTailPrimitiveRecursive.comp (Primrec.const (rawNoteEncode z.1)) Primrec.id).to_comp
  have heq : (fun n : Nat => evaluatorWith ctrl (encodedFiniteTail (rawNoteEncode z.1) n)) =
      (fun n : Nat => ParametricActualCollapse.collapseWith ctrl (fixedHead c + (n : Ordinal))) := by
    funext n
    rw [(encodedFiniteTailCorrect z n).1, ev.2.2.2.2, (finiteTailCorrect z n).1, hz]
  rwa [heq] at hc

theorem circuitComputable : SelectedGeneratedSourceTargets.CircuitComputable := by
  intro ctrl K hctrl ι index s
  induction s with
  | one => exact Computable.const 1
  | var x =>
    exact (Primrec.succ.comp ((Primrec.list_getD 0).comp Primrec.id (Primrec.const (index x)))).to_comp
  | add a b iha ihb => exact Computable.nat_add.comp (iha.pair ihb)
  | shift c a ih => exact (fixedHeads ctrl K hctrl c).2.2.2.2.comp ih

theorem scalarPositive (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    {ι : Type} (s : Scalar ι) (ρ : ι → Nat) (hp : ∀ x, 0 < ρ x) :
    0 < scalarValueWith ctrl ρ s := by
  induction s with
  | one => exact Nat.zero_lt_one
  | var x => exact hp x
  | add a b iha ihb => exact Nat.add_pos_left iha _
  | shift c a ih =>
    have h := (selectedCollapseEstimates ctrl (SelectedGradedPositivityProof.selected_forms hc)).2.2.2.1
      (fixedHead c) (scalarValueWith ctrl ρ a) (fixedHeads ctrl K hc c).2.2.2.1
    exact ih.trans_le ((Nat.le_add_left _ _).trans h)

end LogicLineages.PermittedControl.SelectedGeneratedSourceHeadsProof
