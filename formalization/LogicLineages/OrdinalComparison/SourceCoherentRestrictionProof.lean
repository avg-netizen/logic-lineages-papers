module
public import LogicLineages.OrdinalComparison.SourceCoherentRestrictionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceCoherentRestrictionProof
open SourceCoherentTables SourceCoherentTablesProof SourceCoherentRestriction SourceCoherentRestrictionTargets

theorem restrictionCoherence : RestrictionCoherence := by
  intro I J A B _ _ D φ f hf
  exact ⟨fun j => hf.1 (φ j), fun j k => hf.2 (φ j) (φ k)⟩

theorem rawRestrictionLattice : RawRestrictionLattice := by
  intro I J A B _ _ φ S
  constructor
  · funext j x
    change (sSup S) (φ j) x = (sSup (rawRestriction φ '' S)) j x
    rw [sSup_image]
    simp only [sSup_eq_iSup, iSup_apply, rawRestriction]
  · funext j x
    change (sInf S) (φ j) x = (sInf (rawRestriction φ '' S)) j x
    rw [sInf_image]
    simp only [sInf_eq_iInf, iInf_apply, rawRestriction]

def restrictionFunction {I J : Type} {A B : I → Type}
    [∀ i, Preorder (A i)] [∀ i, CompleteLattice (B i)]
    (D : Diagram I A B) (φ : J → I) (f : coherentSublattice D) :
    coherentSublattice (pullbackDiagram D φ) :=
  ⟨rawRestriction φ f.val, restrictionCoherence I J A B D φ f.val f.property⟩

def restrictionHom {I J : Type} {A B : I → Type}
    [∀ i, Preorder (A i)] [∀ i, CompleteLattice (B i)]
    (D : Diagram I A B) (φ : J → I) :
    CompleteLatticeHom (coherentSublattice D) (coherentSublattice (pullbackDiagram D φ)) where
  toFun := restrictionFunction D φ
  map_sSup' S := by
    apply Subtype.ext
    change rawRestriction φ (sSup ((fun f : coherentSublattice D => f.val) '' S)) =
      sSup ((fun f : coherentSublattice (pullbackDiagram D φ) => f.val) '' (restrictionFunction D φ '' S))
    calc
      _ = sSup (rawRestriction φ '' ((fun f : coherentSublattice D => f.val) '' S)) :=
        (rawRestrictionLattice I J A B φ _).1
      _ = _ := by
        congr 1
        rw [Set.image_image, Set.image_image]
        rfl
  map_sInf' S := by
    apply Subtype.ext
    change rawRestriction φ (sInf ((fun f : coherentSublattice D => f.val) '' S)) =
      sInf ((fun f : coherentSublattice (pullbackDiagram D φ) => f.val) '' (restrictionFunction D φ '' S))
    calc
      _ = sInf (rawRestriction φ '' ((fun f : coherentSublattice D => f.val) '' S)) :=
        (rawRestrictionLattice I J A B φ _).2
      _ = _ := by
        congr 1
        rw [Set.image_image, Set.image_image]
        rfl

theorem actualCoherentRestrictionHom : ActualCoherentRestrictionHom := by
  intro I J A B _ _ D φ
  exact ⟨restrictionHom D φ, fun _ => rfl⟩

theorem finiteRestrictionMembership : FiniteRestrictionMembership := by
  intro I J A B _ _ _ _ _ _ _ _ _ _ _ _ D φ f hf
  apply (coherentFiniteEnumeration J (fun j => A (φ j)) (fun j => B (φ j))
    (pullbackDiagram D φ) (rawRestriction φ f)).mpr
  exact restrictionCoherence I J A B D φ f ((coherentFiniteEnumeration I A B D f).mp hf)

end LogicLineages.OrdinalComparison.Source.SourceCoherentRestrictionProof
