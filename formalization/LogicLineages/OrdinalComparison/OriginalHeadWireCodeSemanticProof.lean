module
public import LogicLineages.OrdinalComparison.OriginalHeadWireCodeScalarProof
public import LogicLineages.OrdinalComparison.PaidHeadTransportProof
public import LogicLineages.OrdinalComparison.UnitArithmeticFormulaCodeProof
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeTypesProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.OriginalHeadWireCode.Proof
open Arithmetic ArithmeticCode FormulaConstruction ForwardTranslation OriginalDomain

private theorem scalar_observation {Γ : List Ty} {τ : Ty} (t : OriginalTerm Γ τ)
    (u : OrdinalVector Γ τ.level)
    (hu : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some u)
    (hf : ∀ ρ, expressionValue (UnitObservation.substitution ρ) (u 0) = (scalarValue u ρ : Ordinal))
    (ρ : Variable Γ .ground → Nat) (n : Nat) :
    (∃ v : OrdinalVector Γ τ.level,
      AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some v ∧
      expressionValue (UnitObservation.substitution ρ) (v 0) = (n : Ordinal)) ↔ scalarValue u ρ=n := by
  constructor
  · rintro ⟨v,hv,he⟩
    have hvu : v=u := Option.some.inj (hv.symm.trans hu)
    subst v
    rw [hf] at he
    exact_mod_cast he
  · intro he
    exact ⟨u,hu,(hf ρ).trans (congrArg (fun n : Nat => (n:Ordinal)) he)⟩

private theorem lifted_codes (xs : List Expr) :
    (xs.map exprCode).map (liftCode 2) = (xs.map (Expr.lift 2)).map exprCode := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro a ha
  exact ArithmeticCode.Proof.exactExpressionLift 2 a

attribute [local irreducible] GraphCode.graphCode

theorem actualOriginalWire : Targets.ActualOriginalWire := by
  intro Γ Θ σ τ hσ B C K
  obtain ⟨uB,hB,hBfin⟩ := actualScalarFiniteness Γ (.arrow σ τ) B
  obtain ⟨uC,hC,hCfin⟩ := actualScalarFiniteness Γ σ C
  obtain ⟨uK,a,c,q,hconst,hrsrc,hbuild,hcodes,hgraph⟩ :=
    GraphCode.Proof.actualEffectiveWholeGraph Θ K
  obtain ⟨u',a',c',v,hconst',hv,hhead,hscalar,hray⟩ := ActualUnaryRay.Proof.actualSourceRay Θ K
  have hu : u'=uK := Option.some.inj (hconst'.1.symm.trans hconst.1)
  subst u'
  have ha : a'=a := Option.some.inj (hconst'.2.1.symm.trans hconst.2.1)
  subst a'
  refine ⟨uB,uC,uK,hB,hC,hconst.1,fun ρ => ⟨hBfin ρ,hCfin ρ⟩,?_⟩
  intro b δ hbudget hpaid xs y hlen
  have hxi : PaidHeadTransport.paidHead (originalPaidValue σ τ hσ b uB uC) = shiftedHead a δ := by
    rw [hhead (fun _ => 0)] at hpaid
    rw [PaidHeadTransport.paidHead,hpaid,
      PaidHeadTransport.Proof.exactOmegaFiniteTail a.evaluate.1.repr (normalRepresentationSound a.evaluate) δ]
    rfl
  obtain ⟨fB,hfB,heB⟩ := UnitArithmeticFormulaCode.Proof.actualSourceFormula Γ (.arrow σ τ) B
    (xs.map (Expr.lift 2)) (.variable 1) (by simpa using hlen)
  obtain ⟨fC,hfC,heC⟩ := UnitArithmeticFormulaCode.Proof.actualSourceFormula Γ σ C
    (xs.map (Expr.lift 2)) (.variable 0) (by simpa using hlen)
  let w := wireExpr (actualOrdinalNorm (shiftedHead a δ)) σ.level
  let g := graph (UnitElimination.realize q) a c δ w (y.lift 2)
  refine ⟨combine fB fC g,?_,?_⟩
  · have hcheckB := (SyntaxCode.Proof.typedCheckExact Γ (.arrow σ τ) (SyntaxCode.encodeTerm B)).mpr ⟨B,rfl⟩
    have hcheckC := (SyntaxCode.Proof.typedCheckExact Γ σ (SyntaxCode.encodeTerm C)).mpr ⟨C,rfl⟩
    have hguard : SyntaxCode.typeCode (.arrow σ τ) ≠ 0 ∧
        (SyntaxCode.typeCode (.arrow σ τ)-1).unpair.1=SyntaxCode.typeCode σ ∧
        0<SyntaxCode.typeLevel (SyntaxCode.typeCode σ) := by
      rw [SyntaxCode.Proof.typeLevelExact]
      simpa [SyntaxCode.typeCode, SyntaxCode.arrowCode] using hσ
    unfold compileCode
    rw [hcheckC]
    simp only [bind, pure, Option.bind_some]
    rw [hcheckB]
    simp only [Option.bind_some, hguard, ↓reduceIte]
    rw [hcodes]
    simp only [Option.bind_some]
    rw [lifted_codes]
    change UnitArithmeticFormulaCode.sourceFormulaCode _ _ _ (exprCode (.variable 1)) >>= _ = _
    rw [hfB]
    simp only [bind, pure, Option.bind_some]
    change UnitArithmeticFormulaCode.sourceFormulaCode _ _ _ (exprCode (.variable 0)) >>= _ = _
    rw [hfC]
    simp only [bind, pure, Option.bind_some]
    rw [(GraphCode.Proof.exactGenuineConstants a c δ).2.1, SyntaxCode.Proof.typeLevelExact,
      ArithmeticCode.Proof.exactExpressionLift]
    simp only [List.length_map]
    change some (combineCode (formulaCode fB) (formulaCode fC)
      (GraphCode.graphCode Θ.length (closedPositiveCode a) c δ
        (UnitEliminationTreeCode.code (UnitElimination.realize q)) (exprCode w) (exprCode (y.lift 2)))) = _
    rw [GraphCode.Proof.exactFormulaCompilation]
    rfl
  · intro ν
    rw [hxi]
    have hb (n m : Nat) : fB.eval (extend (extend ν n) m) ↔ scalarValue uB (inputValues ν xs)=n := by
      rw [heB, Arithmetic.Proof.input_lift_two]
      simp only [Expr.value,extend]
      exact scalar_observation B uB hB hBfin _ n
    have hc (n m : Nat) : fC.eval (extend (extend ν n) m) ↔ scalarValue uC (inputValues ν xs)=m := by
      rw [heC, Arithmetic.Proof.input_lift_two]
      simp only [Expr.value,extend]
      exact scalar_observation C uC hC hCfin _ m
    have hg (n m : Nat) : g.eval (extend (extend ν n) m) ↔
        actualOrdinalNorm (shiftedHead a δ) ≤ actualOrdinalNorm (shiftedHead a δ)+n+m+σ.level ∧
        y.value ν = actualHeadValue (shiftedHead a δ) (actualOrdinalNorm (shiftedHead a δ)+n+m+σ.level) := by
      rw [(hgraph δ w (y.lift 2)).2]
      simp only [w,wireExpr,Expr.value,extend,Arithmetic.Proof.lift_two]
    have hnorm : actualOrdinalNorm (shiftedHead a δ) ≤
        originalWire (shiftedHead a δ) σ.level uB uC (inputValues ν xs) := by
      unfold originalWire
      omega
    refine ⟨hnorm,?_⟩
    simp only [combine,Formula.eval,conjunction,List.foldr_cons,List.foldr_nil]
    simp only [hb,hc,hg]
    simp only [and_true]
    constructor
    · rintro ⟨n,m,hn,hm,hle,he⟩
      subst n
      subst m
      exact he
    · intro he
      exact ⟨scalarValue uB (inputValues ν xs),scalarValue uC (inputValues ν xs),rfl,rfl,hnorm,he⟩
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.OriginalHeadWireCode.Proof
