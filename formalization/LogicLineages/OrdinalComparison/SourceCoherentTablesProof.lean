module
public import LogicLineages.OrdinalComparison.SourceCoherentTablesTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceCoherentTablesProof
open SourceCoherentTables SourceCoherentTablesTargets

theorem coherentValidityTest : CoherentValidityTest := by
  intro I A B _ _ _ _ _ _ _ _ _ _ D f
  simp [validityTest]

theorem coherentFiniteEnumeration : CoherentFiniteEnumeration := by
  intro I A B _ _ _ _ _ _ _ _ _ _ D f
  simp [finiteTables, validityTest]

theorem coherentArbitraryClosure : CoherentArbitraryClosure := by
  intro I A B _ _ D S hs
  constructor
  · constructor
    · intro i x y hxy
      simp only [sSup_apply, iSup_apply]
      exact iSup_mono (fun f : S => (hs f.val f.property).1 i hxy)
    · intro i j
      by_cases h : D.extension i j = true
      · simp only [dif_pos h]
        intro x
        simp only [sSup_apply, iSup_apply, map_iSup]
        apply iSup_congr
        intro f
        have hn : ∀ y, D.outputMap i j h (f.val i y) = f.val j (D.inputMap i j h y) := by
          simpa only [dif_pos h] using (hs f.val f.property).2 i j
        exact hn x
      · simp only [dif_neg h]
  · constructor
    · intro i x y hxy
      simp only [sInf_apply, iInf_apply]
      exact iInf_mono (fun f : S => (hs f.val f.property).1 i hxy)
    · intro i j
      by_cases h : D.extension i j = true
      · simp only [dif_pos h]
        intro x
        simp only [sInf_apply, iInf_apply, map_iInf]
        apply iInf_congr
        intro f
        have hn : ∀ y, D.outputMap i j h (f.val i y) = f.val j (D.inputMap i j h y) := by
          simpa only [dif_pos h] using (hs f.val f.property).2 i j
        exact hn x
      · simp only [dif_neg h]

/-- The actual complete sublattice, constructed only after closure is proved. -/
def coherentSublattice {I : Type} {A B : I → Type} [∀ i, Preorder (A i)]
    [∀ i, CompleteLattice (B i)] (D : Diagram I A B) : CompleteSublattice (Raw I A B) :=
  CompleteSublattice.mk' {f | Coherent D f}
    (fun S hs => (coherentArbitraryClosure I A B D S hs).1)
    (fun S hs => (coherentArbitraryClosure I A B D S hs).2)

theorem actualCoherentSublattice : ActualCoherentSublattice := by
  intro I A B _ _ D
  exact ⟨coherentSublattice D, fun _ => Iff.rfl⟩

theorem finiteCoherentCarrier : FiniteCoherentCarrier := by
  intro I A B _ _ _ _ _ _ _ _ _ _ D
  infer_instance

end LogicLineages.OrdinalComparison.Source.SourceCoherentTablesProof
