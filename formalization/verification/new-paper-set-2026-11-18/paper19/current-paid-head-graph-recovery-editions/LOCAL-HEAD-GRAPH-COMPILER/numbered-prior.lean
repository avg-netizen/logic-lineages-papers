module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphDirectProof
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphInsertedProof
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphFiberCompilerProof
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphFoundationStatementChecks
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphUnitCodeStatementChecks
public import LogicLineages.ControlSensitivityCurrent.CurrentUnitEliminationStatementChecks
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open AdmissibleSum
open CurrentUnitElimination (Tree build render groundCtx oldGround groundOnlyContext HoldsRaw selectGround oldProject)

private theorem literalBlock (p : Policy) (f : Nat→Nat) {Γ σ} (a : OriginalTerm Γ σ)
    (T : Tree Γ) (h : build p (Γ.length+1) a=some T) :
    UnitCode.block p f (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm a) =
      some (Targets.blockCode (render p f T)) := by
  unfold UnitCode.block
  rw [List.length_map,UnitCode.exactUnitBlock p f (Γ.length+1) Γ σ a,h]
  rfl

private theorem pointCodes (f : Nat→Nat) (ξ : Ordinal) (base q : Nat)
    (hn : rawNormCode q=actualOrdinalNorm ξ)
    (h : ∀ t : Nat, actualOrdinalNorm ξ ≤ t → valueCode f q t=J f ξ t) :
    pointValuesCode f q base=exactPoints f ξ base := by
  unfold pointValuesCode exactPoints
  rw [hn]
  apply List.map_congr_left
  intro i hi
  apply h
  omega

/-- Full current graph, for any actual paid certificate at its actual original
box. The finite-section computations return those very open typed formulas. -/
theorem exactNumbered : Targets.ExactNumbered := by
  intro p f hc hf Γ Ξ σ τ B C K b δ paid
  let Kctx := FreshCtx Ξ
  let β := paid.baseHead
  let ξ := shiftHead β δ
  let nξ := actualOrdinalNorm ξ
  have hP := exactOriginalPayment p f Γ Ξ σ τ B C K b δ paid
  have hPaid := hP.2.2.1
  have hN := congrArg actualOrdinalNorm hPaid
  obtain ⟨βn,ξn,c,hparams,hβv,hξv,hcVal,hβn,hξn,heval⟩ :=
    exactParameters p f hc hf Ξ K paid.Kvector paid.assignK δ
  change βn.1.repr=β at hβv
  change ξn.1.repr=ξ at hξv
  change rawNormCode (rawNoteEncode βn.1)=actualOrdinalNorm β at hβn
  change rawNormCode (rawNoteEncode ξn.1)=nξ at hξn
  change (∀ t, nξ≤t → valueCode f (rawNoteEncode ξn.1) t=J f ξ t) at heval
  obtain ⟨c',wv,hassign,hcVal',hclose,hRays⟩ := exactRay p f Ξ K paid.Kvector paid.assignK
  have he : c'=c := by exact_mod_cast hcVal'.symm.trans hcVal
  subst c'
  let base := RayBase β c
  let χ := .ground :: Kctx
  let ray := raySource K
  obtain ⟨QB,hQB,_,_,_,obsB⟩ := CurrentUnitElimination.StatementChecks.exact_actual_open_source_graph p f hf Γ (.arrow σ τ) B
  obtain ⟨QC,hQC,_,_,_,obsC⟩ := CurrentUnitElimination.StatementChecks.exact_actual_open_source_graph p f hf Γ σ C
  obtain ⟨QK,hQK,_,_,_,obsK⟩ := CurrentUnitElimination.StatementChecks.exact_actual_open_source_graph p f hf χ .ground ray
  let gB := render p f QB
  let gC := render p f QC
  let gK := render p f QK
  let G := typedDirect (groundOnlyContext Kctx) f β c δ gK
  let I := inserted (groundOnlyContext Γ) nξ σ.level gB gC G
  have hR (ρ : Variable (.ground :: groundCtx Kctx) .ground→Nat) (v : Nat) :
      HoldsRaw p f gK ρ v ↔ v=J f β (base+ρ .here) := by
    let μ : Variable χ .ground→Nat := fun x => ρ (selectGround x)
    have hr := (obsK μ).1 v
    change HoldsRaw p f gK (fun x => μ (oldGround x)) v ↔ _ at hr
    have hval : (fun x => μ (oldGround x))=ρ := by
      funext x
      change ρ (selectGround (oldGround x))=ρ x
      rw [oldProject]
    rw [hval] at hr
    exact hr.trans (hRays μ v)
  have hGraph (t y : Nat) : G.holds p f (endValues t y) ↔ nξ≤t ∧ y=J f ξ t :=
    exactDirectTemplate p f hf β hP.1 hP.2.1 c δ (groundCtx Kctx) (groundOnlyContext Kctx) gK hR t y
  have hcp := literalBlock p f ray QK hQK
  have hcb := literalBlock p f B QB hQB
  have hcc := literalBlock p f C QC hQC
  let k : KInput := (Ξ.map SyntaxCode.typeCode,SyntaxCode.encodeTerm K,δ)
  let data : OriginalInput := (Γ.map SyntaxCode.typeCode,SyntaxCode.encodeTerm B,SyntaxCode.encodeTerm C,k)
  have haux := (exactFreshAuxiliary.2 Ξ K).2
  have hpop : groundCount ((χ.map SyntaxCode.typeCode).tail)=(groundCtx Kctx).length := by
    change groundCount (Kctx.map SyntaxCode.typeCode) = _
    exact countGround Kctx
  have hpoints := pointCodes f ξ base (rawNoteEncode ξn.1) hξn heval
  have hG : directPacket p f k=some (presentedCode G,nξ) := by
    unfold directPacket k
    simp only [hparams,haux,bind,Option.bind_some,pure,show ray=raySource K from rfl]
    change (UnitCode.block p f (χ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm ray)).bind _ = _
    rw [hcp,Option.bind_some,hβn,hξn,hpop,hpoints]
    have hg := exactTemplateCodes.1 (groundCtx Kctx) (groundOnlyContext Kctx) δ nξ base
      (smallValues f) (exactPoints f ξ base) gK
    rw [hg]
    rfl
  have hI : insertCode p f data=some (presentedCode I) := by
    have hs := (SyntaxCode.StatementChecks.typedCheckExact Γ σ (SyntaxCode.encodeTerm C)).mpr ⟨C,rfl⟩
    unfold insertCode data
    simp only [hs,hcb,hcc,hG,bind,Option.bind_some,pure,SyntaxCode.Proof.typeLevelExact,countGround]
    have hi := exactTemplateCodes.2 (groundCtx Γ) (groundOnlyContext Γ) nξ σ.level gB gC G
    rw [hi]
    rfl
  have hG' : directCode p f k=some (presentedCode G) := by rw [directCode,hG]; rfl
  refine ⟨G,I,hG',hI,?_,?_,?_⟩
  · intro t y
    rw [hPaid]
    exact hGraph t y
  · intro t ht
    rw [hPaid] at ht
    refine ⟨J f ξ t,(hGraph t _).mpr ⟨ht,rfl⟩,fun y h => (hGraph t y).mp h |>.2⟩
  · intro ρ y
    let F := fun x : Variable (groundCtx Γ) .ground => ρ (oldGround x)
    rw [exactInsertedTemplate p f (groundCtx Γ) (groundOnlyContext Γ) nξ σ.level gB gC G F y]
    constructor
    · rintro ⟨B₀,C₀,hB,hC,hY⟩
      have hb := ((obsB ρ).1 B₀).mp hB
      have hc := ((obsC ρ).1 C₀).mp hC
      apply ((hP.2.2.2 ρ).2.2 B₀ C₀ y hb hc).mpr
      rw [hPaid]
      exact (hGraph (nξ+B₀+C₀+σ.level) y).mp hY |>.2
    · intro hY
      obtain ⟨B₀,_,hB⟩ := CurrentAbsolute.scalar_total p f (ExistentialPlan.inputs ρ) B
      obtain ⟨C₀,_,hC⟩ := CurrentAbsolute.scalar_total p f (ExistentialPlan.inputs ρ) C
      refine ⟨B₀,C₀,((obsB ρ).1 B₀).mpr hB,((obsC ρ).1 C₀).mpr hC,?_⟩
      have hy := ((hP.2.2.2 ρ).2.2 B₀ C₀ y hB hC).mp hY
      rw [hPaid] at hy
      apply (hGraph (nξ+B₀+C₀+σ.level) y).mpr
      exact ⟨by omega,hy⟩

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
