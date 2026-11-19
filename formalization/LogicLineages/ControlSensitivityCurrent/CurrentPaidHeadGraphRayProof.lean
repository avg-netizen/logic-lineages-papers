module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphPaymentProof
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphIndexProof
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverageStatementChecks
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsStructuralProof
public import LogicLineages.OrdinalComparison.GroundCaptureClosingCodeStatementChecks
public import LogicLineages.OrdinalComparison.ContextInsertionCodeStatementChecks
public import LogicLineages.OrdinalComparison.WWUnaryCarrierProof
public import LogicLineages.OrdinalComparison.ParametricSourceSuccessorDenotationProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open AdmissibleSum AdmissibleAssignment ParametricSourceSuccessor
open CurrentUnaryChain (commonUnits)
open RawSourceDAG (variableIndex encode)

theorem exactFreshAuxiliary : Targets.ExactFreshAuxiliary := by
  constructor
  · intro Γ
    refine ⟨?_,?_,?_⟩
    · intro x y h
      have hidx := congrArg variableIndex h
      rw [freshGroundIndex,freshGroundIndex,groundRankIndex,groundRankIndex] at hidx
      have he := indexInj hidx
      rw [← CurrentUnitElimination.projectOld Γ x,← CurrentUnitElimination.projectOld Γ y,he]
    · intro x
      rw [freshGroundIndex]
      exact (groundRank x).isLt
    · intro σ τ x
      exact shiftedIndex _ x
  · intro Γ K
    refine ⟨UnaryCarrier.Proof.closeGround_no_ground (freshCopy K),?_⟩
    let d := CurrentTreeInputCoverage.input K
    have h := CurrentTreeInputCoverage.StatementChecks.actual_tree_codes Γ (Ty.curriedGround 1) K
    have hg : RawSourceDAG.Operations.renameCode (freshContext (Γ.map SyntaxCode.typeCode))
        (freshTable (Γ.map SyntaxCode.typeCode)) (encode ⟨Γ,Ty.curriedGround 1,d⟩) =
      encode ⟨FreshCtx Γ,Ty.curriedGround 1,ScopedDAG.renameInput (freshRename Γ) d⟩ := by
      rw [freshContextExact,freshTableExact,RawSourceDAG.Operations.rename_input]
    have he : CurrentTreeCode.expand
        (encode ⟨FreshCtx Γ,Ty.curriedGround 1,ScopedDAG.renameInput (freshRename Γ) d⟩) =
      SyntaxCode.encodeTerm (freshCopy K) := by
      rw [CurrentTreeCode.exactExpansion,(ScopedDAG.StatementChecks.renaming Γ (FreshCtx Γ)
        (Ty.curriedGround 1) (freshRename Γ) d).1,h.1]
      rfl
    have hc : GroundCaptureClosingCode.sourceCode ((FreshCtx Γ).map SyntaxCode.typeCode) 0
        (SyntaxCode.encodeTerm (freshCopy K)) = SyntaxCode.encodeTerm (zeroCopy K) :=
      GroundCaptureClosingCode.StatementChecks.exact_protected_source [] (FreshCtx Γ) (Ty.curriedGround 1) _
    have hi : ContextInsertionCode.sourceCode 0 1 (SyntaxCode.encodeTerm (zeroCopy K)) =
        SyntaxCode.encodeTerm ((zeroCopy K).rename (fun x => .there x)) :=
      ContextInsertionCode.StatementChecks.exact_source_insertion [] [.ground] (FreshCtx Γ) (Ty.curriedGround 1) _
    unfold auxiliaryCode
    simp only [h.2.1,bind,Option.bind_some,pure,hg,he,freshContextExact,hc,hi]
    rfl

private theorem closedValue (f : Nat → Nat) {Γ} (e : OrdinalExpression Γ)
    (ρ : Variable Γ .ground → Nat) :
    denoteWith f (commonUnits ρ) (GroundClosing.expression (UnaryCarrier.groundMap Γ) e) = atUnits f e := by
  induction e with
  | var c =>
    rcases c with ⟨σ,x,j⟩
    cases σ <;> rfl
  | zero | one | omega => rfl
  | add a b ha hb | emul a b ha hb | collapse a b ha hb =>
    simp only [GroundClosing.expression,substitute,denoteWith,atUnits] at *
    rw [ha,hb]

private theorem renameValue (f : Nat → Nat) {Γ Ξ} (r : Renaming Γ Ξ)
    (ν : OrdinalComponent Ξ → Ordinal) (e : OrdinalExpression Γ) :
    denoteWith f ν (ordinalExpressionRename r e) =
      denoteWith f (fun c => ν (ordinalComponentRename r c)) e :=
  ParametricSourceSuccessor.Proof.exactSubstitution _ _ f ν
    (fun c => .var (ordinalComponentRename r c)) e

private theorem liftedUnits (f : Nat → Nat) {Γ} (e : OrdinalExpression Γ)
    (ρ : Variable (.ground::Γ) .ground → Nat) :
    denoteWith f (commonUnits ρ) (ordinalExpressionRename (fun x => .there x) e) =
      denoteWith f (commonUnits (fun x => ρ (.there x))) e := by
  rw [renameValue]
  congr 1
  funext x
  rcases x with ⟨σ,x,j⟩
  cases σ <;> rfl

theorem exactRay : Targets.ExactRay := by
  intro p f Γ K u hu
  have hgen := generatedAt p K u hu 0
  obtain ⟨c,hc⟩ := (GenericScalar.generatedPositiveFinite f Γ (fun _ => 0) 0 (u 0) hgen).2 rfl
  let X := FreshCtx Γ
  let w₀ : OrdinalVector X 1 := SourceRenaming.renameVector (freshRename Γ) u
  let w : OrdinalVector X 1 := GroundClosing.vector (UnaryCarrier.groundMap X) w₀
  have hf : assignment p (freshCopy K)=some w₀ := by
    rw [freshCopy,SourceRenaming.Proof.assignmentNaturality,hu]
    rfl
  have hw : assignment p (zeroCopy K)=some w := by
    rw [zeroCopy,UnaryCarrier.closeGround,GroundClosing.StatementChecks.assignmentNaturality,hf]
    rfl
  have hval (μ : Variable X .ground → Nat) (j : Fin 2) :
      denoteWith f (commonUnits μ) (w j)=atUnits f (u j) := by
    change denoteWith f (commonUnits μ) (GroundClosing.expression (UnaryCarrier.groundMap X)
      (ordinalExpressionRename (freshRename Γ) (u j))) = _
    rw [closedValue]
    exact renameValue f (freshRename Γ) (fun _ => 1) (u j)
  refine ⟨c,w,hw,hc,fun μ => ⟨hval μ 1,(hval μ 0).trans hc⟩,?_⟩
  intro ρ v
  let ws : OrdinalVector (.ground :: X) 1 := SourceRenaming.renameVector (fun x => .there x) w
  let z : OrdinalVector (.ground :: X) 0 := fun j => .var ⟨.ground,.here,j⟩
  let a := application (σ:=.ground) (τ:=.ground) p ws z
  have ha : assignment p (raySource K)=some a := by
    have hws : assignment p ((zeroCopy K).rename (fun x => .there x))=some ws := by
      rw [SourceRenaming.Proof.assignmentNaturality,hw]
      rfl
    simp only [raySource,assignment,hws,Option.bind_some,a,z] <;> rfl
  have hh : denoteWith f (commonUnits ρ) (ws 1)=atUnits f (u 1) :=
    (liftedUnits f (w 1) ρ).trans (hval _ 1)
  have hs : denoteWith f (commonUnits ρ) (ws 0)=(c : Ordinal) :=
    (liftedUnits f (w 0) ρ).trans ((hval _ 0).trans hc)
  rw [scalarWithAssignment p f ρ _ a ha]
  change (ParametricActualCollapse.collapseWith f (ordinalNaturalSum
    (ordinalNaturalProduct Ordinal.omega0 (denoteWith f (commonUnits ρ)
      (ordinalBoxPositive 0 (ordinalVectorAt ws) (ordinalVectorAt z) 1)))
    (ordinalNaturalSum (denoteWith f (commonUnits ρ) (ws 0)) ((ρ .here+1 : Nat) : Ordinal))) : Ordinal) =
      (v : Ordinal) ↔ _
  have hb : ordinalBoxPositive 0 (ordinalVectorAt ws) (ordinalVectorAt z) 1=ws 1 := by
    rw [ordinalBoxPositive,dif_neg (by decide : ¬1≤0)]
    rfl
  rw [hb,hh,hs,LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof.naturalSum_finite,
    actualNaturalSumFiniteRight]
  let beta := ordinalNaturalProduct Ordinal.omega0 (atUnits f (u 1))
  have he : RayBase beta c+ρ .here-actualOrdinalNorm beta=c+(ρ .here+1) := by
    unfold RayBase
    omega
  change (ParametricActualCollapse.collapseWith f (beta+((c+(ρ .here+1) : Nat) : Ordinal)) : Ordinal) =
    (v : Ordinal) ↔ v = J f beta (RayBase beta c+ρ .here)
  unfold J actualHeadInitial
  rw [he]
  exact ⟨fun eq => by exact_mod_cast eq.symm,fun eq => by exact_mod_cast eq.symm⟩

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
