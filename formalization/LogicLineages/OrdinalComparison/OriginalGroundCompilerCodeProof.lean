module
public import LogicLineages.OrdinalComparison.OriginalGroundCompilerCodePackagingProof
public import LogicLineages.OrdinalComparison.OriginalGroundCompilerCodePrimitiveProof
public import LogicLineages.OrdinalComparison.NumericAccountDataProof
public import LogicLineages.OrdinalComparison.OriginalBudgetCodeProof
public import LogicLineages.OrdinalComparison.OriginalScaleCompilerCodeProof
public import LogicLineages.OrdinalComparison.OriginalGroundDataConstructionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalGroundCompilerCode.Proof
open DeterministicAccountData ScalarCarrierAccounting OriginalDomain OriginalScaleFlatList
open OriginalGroundDataConstruction AdmissibleAssignment

theorem actualOriginalCompiler : Targets.ActualOriginalCompiler := by
  intro k Γ P C hactive
  obtain ⟨u,rs,c,labels,hr,hu,hm,hac⟩ := NumericAccountData.Proof.actualCanonicalSource k Γ 0 P
  obtain ⟨u',hu',hex,hbound⟩ := SourceReserveLowerBound.Proof.actualSourceLowerBound k Γ 0 P
  have he : u' = u := Option.some.inj (hu'.symm.trans hu)
  subst u'
  have hh := (SourceReserveLowerBound.Proof.ground_floor P hactive).trans (hbound labels c hac)
  have hcert := DeterministicAccountData.Proof.exactRecordCertification _ rs labels hm
  have hpaid : 3*rs.length+4 ≤ c := by
    have hlen := hcert.1
    unfold reserve at hh
    omega
  let hraw : ∀ r ∈ rs,r.Assigned := fun r h => (hcert.2.2 r h).1
  obtain ⟨u',B,caller,b,hu',hB,hcaller,hbudget,hb,hfour,hbox,hbval⟩ :=
    OriginalBudgetCode.Proof.actualOriginalBoxBudget k Γ P C hactive
  have he : u' = u := Option.some.inj (hu'.symm.trans hu)
  subst u'
  obtain ⟨u',v,hu',hv,hex,hsound⟩ := AccountSemanticDeterminacy.Proof.actualSourceSoundness k Γ 0 P
  have he : u' = u := Option.some.inj (hu'.symm.trans hu)
  subst u'
  have hab := hB
  change (assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase P)).bind
    (fun w => abstraction OrdinalSyntax.defaultPolicy w) = some B at hab
  rw [hu] at hab
  have hfirst := OriginalGroundDataConstruction.Proof.abstraction_first k Γ u v B hv hab
  have hBval : ∀ ρ : Variable Γ .ground → Nat,
      expressionValue (UnitObservation.substitution ρ) (B (boxFirst k)) =
        sourceSum (operators rs hraw) + (c : Ordinal) := by
    intro ρ
    rw [hfirst,OriginalGroundDataConstruction.Proof.packaged_sum rs hraw labels hm]
    exact hsound labels c hac ρ
  have hp : 3*(operators rs hraw).length+4 ≤ c := by
    rw [(OriginalGroundDataConstruction.Proof.exactPackaging k Γ rs hraw).1]
    exact hpaid
  obtain ⟨caller',vC,hcaller',hSat,hCvalue,K,hcompile,hK,hgap,hbalance⟩ :=
    OriginalScaleCompilerCode.Proof.actualScaledCompiler k Γ (operators rs hraw) C b c hfour hp
  have he : caller' = caller := Option.some.inj (hcaller'.symm.trans hcaller)
  subst caller'
  have hgapcode : OriginalScaleCompilerCode.gapCode b
      ((operators rs hraw).map NumericUnaryChain.operatorCode) c = gap b (operators rs hraw) c := by
    simp [OriginalScaleCompilerCode.gapCode,gap,scale]
  rw [hgapcode] at hgap hbalance
  refine ⟨u,B,caller,b,rs,c,hraw,hr,hu,hB,hcaller,hb,hfour,hpaid,hbox,hbval,
    vC,hSat,hCvalue,K,?_,hK,hgap,?_⟩
  · have hi := TrackedSourceInspectionCode.Proof.actualGrammarInspection k
      (Ty.curriedGround (k+1)::Γ) .here 0 P
    have hcheck := hi.2.1
    change SyntaxCode.check (SyntaxCode.typeCode (Ty.curriedGround (k+1))::Γ.map SyntaxCode.typeCode)
      (SyntaxCode.encodeTerm (TrackedSource.erase P)) = some 0 at hcheck
    have hact := hi.1
    change TrackedSourceInspectionCode.occursCode 0 (SyntaxCode.encodeTerm (TrackedSource.erase P)) =
      TrackedSource.active P at hact
    rw [hactive] at hact
    have hpack := exactRecordPackaging k Γ rs hraw
    have hr' := hr
    simp only [List.map_cons] at hr' hbudget
    unfold compileCode
    rw [if_pos hcheck,hact]
    simp only [↓reduceIte,hr',bind,pure,Option.bind_some,hbudget,hpack]
    rw [hcompile]
    simp only [Option.bind_some,hgapcode]
  · intro ρ μ
    rw [hBval ρ]
    exact hbalance ρ μ
end LogicLineages.OrdinalComparison.Source.OriginalGroundCompilerCode.Proof
