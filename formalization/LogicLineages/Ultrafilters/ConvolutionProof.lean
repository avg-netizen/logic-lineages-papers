module
public import LogicLineages.Ultrafilters.AdmissibleExistenceTargets
@[expose] public section
namespace LogicLineages.Ultrafilters

theorem convolution_mem (p q : Ultrafilter ℝ) (s : Set ℝ) :
    s ∈ convolution p q ↔ {x | translate s x ∈ q} ∈ p := by
  rfl

theorem convolution_laws : Targets.ConvolutionLaws := by
  refine ⟨convolution_mem, ?_, ?_⟩
  · intro p q r
    apply Ultrafilter.ext
    intro s
    have ht (x y : ℝ) : translate s (x + y) = translate (translate s x) y := by
      ext z
      simp only [translate, Set.mem_setOf_eq, add_assoc]
    simp only [convolution_mem]
    have he : {x | translate {x | translate s x ∈ r} x ∈ q} =
        {x | {y | translate (translate s x) y ∈ r} ∈ q} := by
      ext x
      have hi : translate {x | translate s x ∈ r} x =
          {y | translate (translate s x) y ∈ r} := by
        ext y
        change (translate s (x + y) ∈ r) ↔ _
        rw [ht]
        rfl
      change (translate {x | translate s x ∈ r} x ∈ q) ↔
        ({y | translate (translate s x) y ∈ r} ∈ q)
      rw [hi]
    rw [he]
  · intro q
    apply continuous_generateFrom_iff.mpr
    rintro _ ⟨s, rfl⟩
    change IsOpen {p : Ultrafilter ℝ | s ∈ convolution p q}
    simpa only [convolution_mem] using
      (ultrafilter_isOpen_basic {x | translate s x ∈ q})

end LogicLineages.Ultrafilters
