module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphUnitComposeCodeProof
public import LogicLineages.ControlSensitivityCurrent.CurrentOneUnitRawProof
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverageStatementChecks
public import LogicLineages.OrdinalComparison.UnitContextSelectionCodeStatementChecks
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.UnitCode
open LogicLineages.OrdinalComparison.Source
open AdmissibleSum AdmissibleAssignment CurrentOneUnit
open CurrentUnitElimination (OpenGraph Tree groundCtx groundOnlyContext)

private theorem coefficientTotal (p : Policy) {Γ σ τ} (a : OriginalTerm (σ::Γ) τ) :
    ∃ d : Coefficients, typedCoefficients p a = some d := by
  obtain ⟨u,hu,_⟩ := actualAdmissibleAssignmentGenerated _ _ p a
  obtain ⟨w,hw,_⟩ := actualAdmissibleAssignmentGenerated _ _ p (OneUnit.unused a)
  refine ⟨(OneUnit.multiplier u,OneUnit.multiplier w,ordinalHeadFree (u 0)),?_⟩
  simp only [typedCoefficients,hu,hw,bind,Option.bind_some,pure] <;> rfl

private theorem renderLeaf (p : Policy) (f : Nat → Nat) {Γ τ}
    (hg : ∀ σ ∈ Γ, σ = .ground) (a : GroundEquivalence.Input Γ τ) :
    Targets.codeUnitRender p f (Tree.leaf hg a)=typedBlock (CurrentUnitElimination.groundGraph p f hg a) := by
  change typedBlock ((CurrentUnitElimination.groundCtx_of_ground Γ hg).symm ▸
    CurrentUnitElimination.groundGraph p f hg a : OpenGraph (groundCtx Γ)) = _
  exact blockCast _ _

private theorem renderFree (p : Policy) (f : Nat → Nat) (left right : List Ty) (σ : Ty)
    (h : 0 < σ.level) (row : LinearCode) (a : Tree (left++right)) :
    Targets.codeUnitRender p f (Tree.free left right σ h row a) =
      freeBlock (groundCtx (left++right)).length row (Targets.codeUnitRender p f a) := by
  let q := CurrentUnitElimination.render p f a
  change typedBlock ((CurrentUnitElimination.groundCtx_remove left right σ h).symm ▸
    CurrentUnitElimination.freeGraph row q : OpenGraph (groundCtx (left++σ::right))) = _
  exact (blockCast _ _).trans (freeBlockExact (groundOnlyContext _) row q).symm

private theorem renderActive (p : Policy) (f : Nat → Nat) (left right : List Ty) (σ : Ty)
    (h : 0 < σ.level) (row : LinearCode) (a b : Tree (left++right)) :
    Targets.codeUnitRender p f (Tree.active left right σ h row a b) =
      activeBlock (groundCtx (left++right)).length row (Targets.codeUnitRender p f a) (Targets.codeUnitRender p f b) := by
  let l := CurrentUnitElimination.render p f a
  let r := CurrentUnitElimination.render p f b
  change typedBlock ((CurrentUnitElimination.groundCtx_remove left right σ h).symm ▸
    CurrentUnitElimination.activeGraph row l r : OpenGraph (groundCtx (left++σ::right))) = _
  exact (blockCast _ _).trans (activeBlockExact (groundOnlyContext _) row l r).symm

theorem exactUnitBlock : Targets.ExactUnitBlock := by
  intro p f fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro Γ τ a
    rw [blockFuel,UnitContextSelectionCode.StatementChecks.exact_typed_selection,CurrentUnitElimination.build]
    cases hs : UnitElimination.select Γ with
    | ground hg =>
      have ht := (CurrentTreeInputCoverage.StatementChecks.actual_tree_codes Γ τ a).2.1
      simp only [UnitContextSelectionCode.selectionCode,CurrentUnitElimination.step,ht,bind,
        Option.bind_some,pure,Option.map_some,groundBlockExact _ _ hg,renderLeaf]
    | found left right σ hσ =>
      let b := a.rename (SelectedBinder.moveToHead left right σ)
      obtain ⟨d,hd⟩ := coefficientTotal p b
      let row := equation τ.level d
      have hc := CurrentOneUnit.exactSelectedCodes p left right σ τ a d hσ hd
      have hg : groundCount ((left ++ σ :: right).map SyntaxCode.typeCode) = (groundCtx (left++right)).length := by
        rw [countGround,CurrentUnitElimination.groundCtx_remove left right σ hσ]
      have hL := ih (left++right) (.arrow σ τ) (OneUnit.first b)
      have hR := ih (left++right) (.arrow σ (.arrow .ground τ)) (OneUnit.second b)
      have hc' : compileSelected p (left.length,(left++σ::right).map SyntaxCode.typeCode,
          SyntaxCode.encodeTerm a)=some (literalPacket b d) := hc
      simp only [UnitContextSelectionCode.selectionCode,CurrentUnitElimination.step,List.length_map,bind]
      change (compileSelected p (left.length,(left++σ::right).map SyntaxCode.typeCode,
          SyntaxCode.encodeTerm a)).bind _ =
        Option.map (Targets.codeUnitRender p f) ((typedCoefficients p b).bind _)
      rw [hc',hd]
      simp only [Option.bind_some,pure,literalPacket,hg]
      simp only [List.map_append,List.map_cons] at hL hR
      rw [hL]
      cases hfree : d.2.2 <;> cases hq : CurrentUnitElimination.build p fuel (OneUnit.first b) <;>
        simp only [hfree,hq,Bool.false_eq_true,↓reduceIte,bind,Option.bind_some,Option.map_some,
          Option.map_none,Option.bind_none,renderFree,b,row] <;> try rfl
      rw [hR]
      cases ht : CurrentUnitElimination.build p fuel (OneUnit.second b) <;>
        simp only [ht,bind,Option.bind_some,pure,Option.map_some,Option.map_none,Option.bind_none,
          renderActive,b,row] <;> rfl

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.UnitCode
