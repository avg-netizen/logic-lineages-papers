module
public import LogicLineages.ModelsAlgebra.Forests.RankedGraphImageProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedGraphImage.StatementChecks

theorem pruneGraphEmbedding : Targets.PruneGraphEmbedding := Proof.pruneGraphEmbedding

theorem idealImage : Targets.IdealImage := Proof.idealImage

theorem imageCoverFromLanguage : Targets.ImageCoverFromLanguage := Proof.imageCoverFromLanguage

theorem imageCover : Targets.ImageCover := Proof.imageCover

end LogicLineages.ModelsAlgebra.Forests.RankedGraphImage.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.RankedGraphImage
