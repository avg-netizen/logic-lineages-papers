module
public import LogicLineages.OrdinalComparison.OneUnitCodeTargets
public import LogicLineages.OrdinalComparison.ContextInsertionCodeProof
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeTypesProof
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OneUnitCode.Proof

private theorem unused_correct {Γ τ} (a : OriginalTerm Γ τ) :
    unusedCode (SyntaxCode.encodeTerm a) = SyntaxCode.encodeTerm (OneUnit.unused a) := by
  have h := ContextInsertionCode.Proof.exactSourceInsertion [] [.ground] Γ τ a
  change ContextInsertionCode.sourceCode 0 1 (SyntaxCode.encodeTerm a) =
    SyntaxCode.encodeTerm (a.rename (Renaming.weaken Γ .ground)) at h
  exact congrArg (fun n => 8*Nat.pair 0 n+6) h

theorem exactLiteralSyntax : Targets.ExactLiteralSyntax := by
  refine ⟨fun Γ τ a => unused_correct a,?_,?_⟩
  · intro Γ σ τ a
    refine ⟨rfl,?_⟩
    unfold secondCode
    rw [unused_correct]
    rfl
  · intro τ d
    simp only [coefficientCode,constantCode,OneUnit.coefficient,OneUnit.constant,OneUnit.copies]
    rw [SyntaxCode.Proof.typeLevelExact]
    exact ⟨rfl,rfl⟩

private theorem multiplier_correct {Γ σ m} (h : OrdinalVector (σ::Γ) m) :
    multiplierCode (SyntaxCode.typeCode σ) (OrdinalSyntax.vectorCode h) = OneUnit.multiplier h := by
  unfold multiplierCode OneUnit.multiplier
  rw [SyntaxCode.Proof.typeLevelExact]
  congr 1
  simp only [OrdinalSyntax.vectorCode,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext j
  exact OrdinalSyntax.ordinalSyntaxPartialSizeCorrect Γ σ (h j)

private theorem scalar_lookup {Γ m} (h : OrdinalVector Γ m) :
    (OrdinalSyntax.vectorCode h).getD 0 0 = OrdinalSyntax.typedCode (h 0) := by
  simp [OrdinalSyntax.vectorCode,List.getD_eq_getElem?_getD]

theorem exactCompiler : Targets.ExactCompiler := by
  refine ⟨fun Γ σ m h => multiplier_correct h,?_⟩
  intro Γ σ τ a
  have ha := DefaultSourceAssignment.Proof.assignmentCorrect (σ::Γ) τ a
  have hb := DefaultSourceAssignment.Proof.assignmentCorrect (σ::Γ) (.arrow .ground τ) (OneUnit.unused a)
  simp only [List.map_cons] at ha hb
  unfold compileCode OneUnit.compile
  rw [unused_correct,ha,hb]
  cases h : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy a with
  | none => simp [h,bind,pure]
  | some v =>
    cases h' : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (OneUnit.unused a) with
    | none => simp [h,h',bind,pure]
    | some w =>
      simp [h,h',bind,pure,multiplier_correct,scalar_lookup,
        OrdinalSyntax.ordinalSyntaxHeadFreeCorrect,dataCode]
      change OrdinalSyntax.headFree ((OrdinalSyntax.vectorCode v).getD 0 0) = ordinalHeadFree (v 0)
      rw [scalar_lookup,OrdinalSyntax.ordinalSyntaxHeadFreeCorrect]
end LogicLineages.OrdinalComparison.Source.OneUnitCode.Proof
