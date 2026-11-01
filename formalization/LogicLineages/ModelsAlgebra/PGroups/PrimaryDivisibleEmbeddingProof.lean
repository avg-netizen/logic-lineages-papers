module
public import LogicLineages.ModelsAlgebra.PGroups.PrimaryDivisibleEmbeddingTargets
public import LogicLineages.ModelsAlgebra.PGroups.PrueferDirectSumProof
public import LogicLineages.ModelsAlgebra.PGroups.PrueferSocleIsoProof
public import LogicLineages.ModelsAlgebra.PGroups.PrueferEnlargementProof
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleExtensionProof
public import LogicLineages.ModelsAlgebra.PGroups.PrimarySocleControlProof
public import LogicLineages.ModelsAlgebra.PGroups.AdaptedSocleDefinitions
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Data.Finsupp.Encodable
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary
/-- The basis of the actual socle determines a countable Prüfer ambient group.
Only the actual socle map is extended; primary torsion makes the extension injective. -/
theorem countable_primary_divisible_embedding : Targets.countablePrimaryDivisibleEmbedding := by
  classical
  intro p _ T _ _ hT
  let V := pSocle p (⊤ : AddSubgroup T)
  let I := Module.Basis.ofVectorSpaceIndex (ZMod p) V
  let b : Module.Basis I (ZMod p) V := Module.Basis.ofVectorSpace _ _
  letI : Countable I := b.injective.countable
  let E := PrueferDirectSum p I
  letI : Countable (PrueferModel p) := pruefer_model_countable p
  have hcount : Countable E := inferInstance
  obtain ⟨he,ht⟩ := pruefer_direct_sum_nature p I
  obtain ⟨s⟩ := pruefer_socle_iso p
  obtain ⟨c,hc⟩ := pruefer_direct_sum_socle p I s
  let e : V ≃+ pSocle p (⊤ : AddSubgroup E) := b.repr.toAddEquiv.trans c.symm
  let j : V →+ E := (pSocle p (⊤ : AddSubgroup E)).subtype.comp e.toAddMonoidHom
  have hj : Function.Injective j := Subtype.val_injective.comp e.injective
  obtain ⟨i,hi⟩ := divisible_hom_extension T E he (pSocle p ⊤) j
  have hinj : Function.Injective i := primary_socle_injectivity p T E hT i (by
    intro x y hxy
    apply hj
    rw [←hi x,←hi y]
    exact hxy)
  exact ⟨E,inferInstance,hcount,ht,he,i,hinj⟩
end LogicLineages.ModelsAlgebra.PGroups
