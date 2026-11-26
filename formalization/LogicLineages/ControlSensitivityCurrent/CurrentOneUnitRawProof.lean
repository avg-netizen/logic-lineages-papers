module
public import LogicLineages.ControlSensitivityCurrent.CurrentOneUnitInflationProof
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionEmitterSyntaxProof
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverageStatementChecks
public import LogicLineages.ControlSensitivityCurrent.RawPlanCompilerEmbeddingProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadStatementChecks
public import LogicLineages.OrdinalComparison.WWScopedSourceDAGStatementChecks
public import LogicLineages.OrdinalComparison.WWSelectedBinderStatementChecks
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckStatementChecks
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeTypesStatementChecks
public import LogicLineages.StandardControlCurrent.PolicyAssignmentStatementChecks
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentOneUnit

open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open GroundEquivalence

private theorem sameIndex {Γ : List Ty} {τ : Ty} (x : Variable Γ τ) :
    RawSourceDAG.variableIndex x = SourceTypedPorts.variableIndex x := by
  induction x with
  | here => rfl
  | there x ih => simp only [RawSourceDAG.variableIndex, SourceTypedPorts.variableIndex, ih]

private theorem movedTable (left right : List Ty) (σ : Ty) :
    selectedTable left.length ((left ++ σ :: right).map SyntaxCode.typeCode) =
      RawSourceDAG.Operations.renamingCode (SelectedBinder.moveToHead left right σ) := by
  have h := RawSourceDAG.PlanCompiler.renaming_comp_codes
    (fun {τ} (x : Variable (left ++ σ :: right) τ) => x)
    (SelectedBinder.moveToHead left right σ) (slotIndex left.length) (fun x => by
      rw [sameIndex, sameIndex x]
      exact SelectedBinder.StatementChecks.indices left right σ _ x)
  rw [RawSourceDAG.PlanCompiler.identity_table] at h
  simpa only [selectedTable, List.length_map] using h.symm

private theorem splitContext (left right : List Ty) (σ : Ty) :
    let ys := (left ++ σ :: right).map SyntaxCode.typeCode
    ys[left.length]? = some (SyntaxCode.typeCode σ) ∧
    ys.take left.length ++ ys.drop (left.length+1) =
      (left ++ right).map SyntaxCode.typeCode := by
  induction left with
  | nil => exact ⟨rfl,rfl⟩
  | cons a left ih =>
    change ((left ++ σ :: right).map SyntaxCode.typeCode)[left.length]? = _ ∧
      SyntaxCode.typeCode a ::
        (((left ++ σ :: right).map SyntaxCode.typeCode).take left.length ++
          ((left ++ σ :: right).map SyntaxCode.typeCode).drop (left.length+1)) =
      SyntaxCode.typeCode a :: (left ++ right).map SyntaxCode.typeCode
    exact ⟨ih.1, congrArg (List.cons _) ih.2⟩

theorem exactMoveCodes : CurrentOneUnitTargets.ExactMoveCodes := by
  intro left right σ τ a
  have h := splitContext left right σ
  change (((left ++ σ :: right).map SyntaxCode.typeCode)[left.length]? >>= fun t =>
    some (
    RawSourceDAG.Operations.renameCode
      (t :: (((left ++ σ :: right).map SyntaxCode.typeCode).take left.length ++
        ((left ++ σ :: right).map SyntaxCode.typeCode).drop (left.length+1)))
      (selectedTable left.length ((left ++ σ :: right).map SyntaxCode.typeCode))
      (RawSourceDAG.encode ⟨left ++ σ :: right,τ,a⟩))) = _
  rw [h.1]
  simp only [Option.bind_some, h.2, movedTable]
  exact congrArg some (RawSourceDAG.Operations.rename_input
    (SelectedBinder.moveToHead left right σ) a).symm

private theorem codedSize {Γ σ m} (h : OrdinalVector (σ :: Γ) m) :
    codedMultiplier (SyntaxCode.typeCode σ) (OrdinalSyntax.vectorCode h) =
      OneUnit.multiplier h := by
  unfold codedMultiplier OneUnit.multiplier OrdinalSyntax.vectorCode
  rw [SyntaxCode.StatementChecks.typeLevelExact]
  apply congrArg (fun v : List Nat => 2 ^ (σ.level+1)*v.sum)
  simp only [List.map_ofFn, Function.comp_def]
  apply congrArg List.ofFn
  funext j
  exact LogicLineages.OrdinalComparison.StatementChecks.fixed_ordinalSyntaxPartialSizeCorrect Γ σ (h j)

private theorem vectorHead {Γ σ m} (h : OrdinalVector (σ :: Γ) m) :
    (OrdinalSyntax.vectorCode h).head? = some (OrdinalSyntax.typedCode (h 0)) := by
  simp only [OrdinalSyntax.vectorCode, List.ofFn_succ, List.head?_cons] <;> rfl

private theorem unusedCodeExact {Γ τ} (a : OriginalTerm Γ τ) :
    lambdaCode 0 (CurrentTreeCode.expand (CurrentDecisionEmitter.liftCode 1
      (RawSourceDAG.encode ⟨Γ,τ,CurrentTreeInputCoverage.input a⟩))) =
      SyntaxCode.encodeTerm (OneUnit.unused a) := by
  let d := CurrentTreeInputCoverage.input a
  have ht := (CurrentTreeInputCoverage.StatementChecks.actual_tree_codes Γ τ a).1
  rw [CurrentDecisionEmitter.lift_exact, CurrentTreeCode.exactExpansion]
  change lambdaCode 0 (SyntaxCode.encodeTerm
    (ScopedDAG.renameInput (Renaming.weaken Γ .ground) d).term) = _
  rw [(ScopedDAG.StatementChecks.renaming Γ (.ground :: Γ) τ (Renaming.weaken Γ .ground) d).1]
  change lambdaCode 0 (SyntaxCode.encodeTerm (d.term.rename _)) = _
  change d.term = a at ht
  rw [ht]
  rfl

theorem exactHeadCodes : CurrentOneUnitTargets.ExactHeadCodes := by
  intro p Γ σ τ a d hσ hd
  obtain ⟨h,h',_,ha,hu,_,_,_,_,_⟩ := literalInflation p Γ σ τ a
  have hcoeff : d = (OneUnit.multiplier h,OneUnit.multiplier h',ordinalHeadFree (h 0)) := by
    have hv := hd
    simp only [typedCoefficients, ha, hu, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hv
    exact (Option.some.inj hv).symm
  have hτ := (SyntaxCode.StatementChecks.typedCheckExact (σ :: Γ) τ (SyntaxCode.encodeTerm a)).2 ⟨a,rfl⟩
  have hD := (CurrentTreeInputCoverage.StatementChecks.actual_tree_codes (σ :: Γ) τ a).2.1
  have hA := PolicyAssignmentStatementChecks.full.1 p (σ :: Γ) τ a
  have hU := PolicyAssignmentStatementChecks.full.1 p (σ :: Γ) (.arrow .ground τ) (OneUnit.unused a)
  rw [ha, Option.map_some] at hA
  rw [hu, Option.map_some] at hU
  simp only [List.map_cons] at hτ hD hA hU
  have hσcode := SyntaxCode.StatementChecks.typeLevelExact σ
  have hτcode := SyntaxCode.StatementChecks.typeLevelExact τ
  have hfree := LogicLineages.OrdinalComparison.StatementChecks.fixed_ordinalSyntaxHeadFreeCorrect Γ σ (h 0)
  unfold compileHead
  simp only [List.map_cons, List.head?_cons, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, hσcode, hσ, if_pos]
  rw [hτ, Option.bind_some, hD, Option.bind_some, unusedCodeExact, hA, Option.bind_some,
    hU, Option.bind_some, vectorHead, Option.bind_some, hfree, codedSize, codedSize, hτcode, hcoeff] <;> rfl

theorem exactSelectedCodes : CurrentOneUnitTargets.ExactSelectedCodes := by
  intro p left right σ τ a d b hσ hd
  let Γ := left ++ σ :: right
  let Δ := σ :: left ++ right
  let r : Renaming Γ Δ := SelectedBinder.moveToHead left right σ
  let q := CurrentTreeInputCoverage.input a
  have ht := CurrentTreeInputCoverage.StatementChecks.actual_tree_codes Γ τ a
  have hn : CurrentTreeCode.expand (RawSourceDAG.encode ⟨Δ,τ,ScopedDAG.renameInput r q⟩) =
      SyntaxCode.encodeTerm b := by
    rw [CurrentTreeCode.exactExpansion, (ScopedDAG.StatementChecks.renaming Γ Δ τ r q).1]
    have hq : q.term = a := ht.1
    rw [hq] <;> rfl
  unfold compileSelected
  simp only [Option.bind_eq_bind]
  rw [ht.2.1, Option.bind_some, exactMoveCodes left right σ τ q, Option.bind_some]
  change compileHead p (Δ.map SyntaxCode.typeCode,
    CurrentTreeCode.expand (RawSourceDAG.encode ⟨Δ,τ,ScopedDAG.renameInput r q⟩)) = _
  rw [hn]
  exact exactHeadCodes p (left ++ right) σ τ b d hσ hd

end LogicLineages.ControlSensitivityCurrent.CurrentOneUnit
