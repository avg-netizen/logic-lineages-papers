module
public import LogicLineages.PermittedControl.ArbitraryFixedHeadCollapseTargets
import LogicLineages.PermittedControl.ArbitraryFixedHeadCollapseNormalizationProof
import LogicLineages.PermittedControl.FixedHeadCollapseGraphSemanticProof
import LogicLineages.PermittedControl.FunnelProof
import LogicLineages.PermittedControl.CollapseProof
import LogicLineages.OrdinalComparison.RawNormalProof
import LogicLineages.OrdinalComparison.ParametricActualCollapseProof

@[expose] public section
namespace LogicLineages.PermittedControl.ArbitraryFixedHeadCollapse
open OrdinalComparison

private theorem realized (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B) (p : Input)
    (normal : ONote.NF (rawNoteDecode p.1)) :
    read f p = some (ParametricActualCollapse.collapseWith f
      ((rawNoteDecode p.1).repr + (p.2 : Ordinal))) := by
  let a := (rawNoteDecode p.1).repr
  have code : rawNormalCode p.1 = 1 := (rawNormalDecodeCorrect p.1).mpr normal
  have accurate := actualNormalization p normal
  by_cases finite : encodedFiniteTest p.1 = true
  · have source : a + (p.2 : Ordinal) =
        ((encodedFiniteValue p.1 + p.2 : Nat) : Ordinal) := by
      rw [show a = (encodedFiniteValue p.1 : Ordinal) from accurate.2.1 finite,Nat.cast_add]
    have value := ParametricActualCollapse.Proof.finiteValues f
      (control_self_le f (selected_threshold_admissible f B selected).2)
      (encodedFiniteValue p.1 + p.2)
    change read f p = some (ParametricActualCollapse.collapseWith f (a + (p.2 : Ordinal)))
    rw [source,value]
    simp [read,code,finite]
  · have nonfinite : Ordinal.omega0 ≤ a := le_of_not_gt (fun h => finite (accurate.1.mpr h))
    obtain ⟨paid,_,_,_,initial⟩ := accurate.2.2 nonfinite
    have hit := ((FixedHeadCollapseGraph.sourceGraph f B selected (transported p)).1
      (headCollapse f (rawNoteDecode (transported p).1).repr (transported p).2)).mpr ⟨paid,rfl⟩
    rw [headCollapse,initial] at hit
    simpa [read,code,finite] using hit

theorem actualGraph : ActualGraph := by
  intro f B selected p
  by_cases normal : ONote.NF (rawNoteDecode p.1)
  · have hit := realized f B selected p normal
    refine ⟨?_,?_⟩
    · simp [hit,normal]
    · intro y
      constructor
      · intro result
        exact ⟨normal,(Option.some.inj (hit.symm.trans result)).symm⟩
      · rintro ⟨_,rfl⟩
        exact hit
  · have invalid : rawNormalCode p.1 ≠ 1 := fun h => normal ((rawNormalDecodeCorrect p.1).mp h)
    simp [read,invalid,normal]

end LogicLineages.PermittedControl.ArbitraryFixedHeadCollapse
