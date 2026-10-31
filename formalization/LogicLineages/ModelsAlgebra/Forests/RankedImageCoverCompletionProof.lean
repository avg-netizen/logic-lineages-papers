module
public import LogicLineages.ModelsAlgebra.Forests.RankedImageCoverCompletionTargets
public import LogicLineages.ModelsAlgebra.Forests.RankedGraphImageProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedGraphImage.CompletionProof

theorem imageCoverFromIdeals : CompletionTargets.ImageCoverFromIdeals := by
  intro ι _ _ I L hI hL
  have hcover : ∀ G, Image L G ↔ ∃ i, Image (I i) G :=
    Proof.imageCoverFromLanguage ι I L (Image L) hL (fun _ => Iff.rfl)
  exact ⟨hcover, Proof.imageCover ι I (Image L) hI hcover⟩

end LogicLineages.ModelsAlgebra.Forests.RankedGraphImage.CompletionProof
