module
public import LogicLineages.OrdinalComparison.UnitEliminationBuildCodeTargets
public import LogicLineages.OrdinalComparison.UnitContextSelectionCodeProof
public import LogicLineages.OrdinalComparison.UnitGroundBlockCodeProof
public import LogicLineages.OrdinalComparison.SelectedBinderCodeProof
public import LogicLineages.OrdinalComparison.OneUnitCodeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitEliminationBuildCode.Proof
open UnitEliminationTreeCode
attribute [local irreducible] Nat.sqrt Nat.unpair OneUnit.compile

theorem exactFuelBuild : Targets.ExactFuelBuild := by
  intro fuel
  induction fuel with
  | zero => intros;rfl
  | succ fuel ih =>
    intro Γ τ t
    have hc := (SyntaxCode.Proof.typedCheckExact Γ τ (SyntaxCode.encodeTerm t)).mpr ⟨t,rfl⟩
    rw [buildCode,hc]
    simp only [bind,pure,Option.bind_some]
    rw [UnitContextSelectionCode.Proof.exactTypedSelection]
    cases hs : UnitElimination.select Γ with
    | ground hΓ =>
      simp only [UnitContextSelectionCode.selectionCode,UnitElimination.build,hs,UnitElimination.step,
        Option.map_some,List.length_map]
      rw [UnitGroundBlockCode.Proof.exactGroundBlock]
      rfl
    | found left right σ hσ =>
      simp only [UnitContextSelectionCode.selectionCode,UnitElimination.build,hs,UnitElimination.step]
      let a := t.rename (SelectedBinder.moveToHead left right σ)
      have hp := SelectedBinderCode.Proof.exactSourcePermutation [] left right σ τ t
      change SelectedBinderCode.sourceCode 0 left.length (SyntaxCode.encodeTerm t) = SyntaxCode.encodeTerm a at hp
      simp only [List.length_map]
      rw [hp]
      have hd := OneUnitCode.Proof.exactCompiler.2 (left++right) σ τ a
      have hf := (OneUnitCode.Proof.exactLiteralSyntax.2.1 (left++right) σ τ a).1
      have hb := (OneUnitCode.Proof.exactLiteralSyntax.2.1 (left++right) σ τ a).2
      have hif := ih (left++right) _ (OneUnit.first a)
      have hib := ih (left++right) _ (OneUnit.second a)
      simp only [List.map_append] at hd hif hib
      rw [hd,hf,hb,hif,hib]
      cases hdata : OneUnit.compile a with
      | none => simp only [hdata,bind,pure,Option.map_none,Option.bind_none]
      | some d =>
        simp only [hdata,Option.map_some,bind,pure,Option.bind_some,OneUnitCode.dataCode]
        have hcoef := OneUnitCode.Proof.exactLiteralSyntax.2.2 τ d
        rw [hcoef.1,hcoef.2]
        cases hfree : d.free <;>
          cases hq : UnitElimination.build fuel (OneUnit.first a) <;>
          cases hr : UnitElimination.build fuel (OneUnit.second a) <;>
          simp only [hdata,hfree,hq,hr,bind,pure,OneUnitCode.dataCode,
            Option.map_none,Option.map_some,Option.bind_none,Option.bind_some,↓reduceIte,
            UnitEliminationTreeCode.code,freeMetadata,activeMetadata] <;> rfl
end LogicLineages.OrdinalComparison.Source.UnitEliminationBuildCode.Proof
