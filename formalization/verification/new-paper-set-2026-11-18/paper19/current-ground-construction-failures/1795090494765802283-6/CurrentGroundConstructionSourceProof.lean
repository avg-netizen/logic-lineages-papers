module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundConstructionChainProof
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundConstructionGapProof
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundAccountSemanticProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundConstruction

open LogicLineages.OrdinalComparison (ordinalNaturalSum ordinalNaturalProduct)
open LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open AdmissibleSum CurrentGroundBudget
open CurrentUnaryChain (commonUnits)
open CurrentReserve (Carrier carrierSum reserve unitValue)
open CurrentGroundAccount (Matches recordCode)
open DeterministicAccountData (UnaryRecord)

private theorem recordFacts (p : Policy) (f : Nat → Nat) {k Γ}
    (rs : List (UnaryRecord (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ)))
    (xs : List (Carrier p)) (hm : List.Forall₂ Matches rs xs) :
    rs.length = xs.length ∧ (∀ op ∈ rs.map carrierOp, op.Assigned p) ∧
      (((rs.map carrierOp).map (fun op => unitValue f (op.vector 1))).foldr ordinalNaturalSum 0) =
        carrierSum f xs := by
  induction hm with
  | nil =>
    exact ⟨rfl,fun op h => by simp at h,rfl⟩
  | @cons r a rs xs h head ih =>
    obtain ⟨ha,hn,he⟩ := h
    subst a
    refine ⟨by simp [ih.1],?_,?_⟩
    · intro o ho
      simp only [List.map_cons,List.mem_cons] at ho
      rcases ho with rfl|ho
      · exact ha
      · exact ih.2.1 o ho
    · change ordinalNaturalSum (unitValue f (r.vector 1))
        (((rs.map carrierOp).map (fun op => unitValue f (op.vector 1))).foldr ordinalNaturalSum 0) =
        ordinalNaturalSum (unitValue f (r.vector 1)) (carrierSum f xs)
      rw [ih.2.2]

private theorem actualPaidList (p : Policy) {Γ} (b : Nat) (xs : List (Operator Γ))
    (caller : Operator Γ) (hs : ∀ o ∈ xs, o.Assigned p) (hc : caller.Assigned p) :
    ∀ o ∈ paidList b xs caller, o.Assigned p := by
  intro o ho
  rw [paidList,List.mem_append] at ho
  rcases ho with ho|ho
  · obtain ⟨ys,hys,hy⟩ := List.mem_flatten.mp ho
    have he := (List.mem_replicate.mp hys).2
    subst ys
    exact hs o hy
  · have he := (List.mem_replicate.mp ho).2
    subst o
    exact hc

private theorem literalTypedConstruction (p : Policy) (f : Nat → Nat) (k : Nat) (Γ : List Ty)
    (P : TrackedSource.Expr k (Ty.curriedGround (k+1) :: Γ) .here 0)
    (C : OriginalTerm Γ (Ty.curriedGround (k+1))) (hAct : TrackedSource.active P = true) :
    CurrentGroundConstructionTargets.SourceResult p f k Γ (TrackedSource.erase P) C := by
  obtain ⟨u,rs,xs,c,v,_,hRaw,hu,hm,hSpawn,_,hFloor,hv,hVal⟩ :=
    CurrentGroundAccount.sourceAccount p f k Γ 0 P
  obtain ⟨u',B,caller,v',b,hu',hB,hC,hv',hB1,hB2,hb,hb4,hbox,hFin,hBudget⟩ :=
    originalBox p k Γ P C hAct
  have huu : u' = u := Option.some.inj (hu'.symm.trans hu)
  subst u'
  have hvv : v' = v := Option.some.inj (hv'.symm.trans hv)
  subst v'
  have hRecords := recordFacts p f rs xs hm
  have h4 := (groundSourceFloor P hAct).trans hFloor
  let cs := rs.map carrierOp
  have hCLen : cs.length = rs.length := by simp [cs]
  have hPaid : 3*cs.length+4 ≤ c := by
    rw [hCLen,hRecords.1]
    unfold reserve at h4
    omega
  obtain ⟨vC,hUC,hCC,hCallerRaw⟩ := actualCaller p Γ k C caller hC
  let opC := callerOp (UnaryCarrier.saturate k C) vC
  have hOpC : opC.Assigned p := hUC
  let ops := paidList b cs opC
  let K := SourceUnaryChain.chainSource (terms ops)
  have hAssigned : ∀ o ∈ ops, o.Assigned p := actualPaidList p b cs opC hRecords.2.1 hOpC
  obtain ⟨_,w,hK,hKRaw,hHead⟩ := exactSingleChain p f Γ ops hAssigned
  obtain ⟨hGap,_,hBalance⟩ := exactPositiveGap Γ f b c cs opC hb4 hPaid
  let Δ := gap b rs.length c
  have hΔ : 0 < Δ := by simpa only [hCLen,Δ] using hGap
  refine ⟨u,B,caller,v,rs,xs,vC,b,c,hu,hB,hC,hv,hSpawn,hm,h4,hRaw,hB1,hB2,hb,hb4,hbox,
    hFin f,hUC,hCC,w,Δ,hK,?_,rfl,hΔ,?_⟩
  · let body : Nat := SyntaxCode.encodeTerm (τ := .ground) (TrackedSource.erase P)
    have hInspect := TrackedSourceInspectionCode.Proof.actualGrammarInspection k
      (Ty.curriedGround (k+1) :: Γ) .here 0 P
    have hc : SyntaxCode.check (SyntaxCode.typeCode (Ty.curriedGround (k+1)) :: Γ.map SyntaxCode.typeCode)
        body = some 0 := hInspect.2.1
    have ho : TrackedSourceInspectionCode.occursCode 0 body = true := hInspect.1.trans hAct
    have hR : rs.map recordCode = cs.map operatorCode := by
      rw [show cs = rs.map carrierOp by rfl,List.map_map]
      rfl
    have hPay := (exactReplication Γ b cs opC).2
    have hR0 := hRaw
    have hB0 := hBudget
    simp only [List.map_cons] at hR0 hB0
    change CurrentGroundAccount.sourceCode p _ body = _ at hR0
    change budgetCode p _ body = _ at hB0
    change compileCode p _ _ body _ = _
    simp only [compileCode,hc,ho,if_true,hR0,hB0,hCallerRaw,bind,pure,Option.bind_some,Prod.mk.injEq]
    rw [hR,hPay,hKRaw]
    simp [Δ,K,ops,cs]
  · intro ρ μ
    have hBody : ParametricSourceSuccessor.denoteWith f (commonUnits ρ) (B (boxFirst k)) =
        carrierSum f xs + (c : Ordinal) := by
      rw [hB1]
      exact hVal ρ
    obtain ⟨caller',hC',hg⟩ := AdmissibleAssignment.actualAdmissibleAssignmentGenerated
      Γ (Ty.curriedGround (k+1)) p C
    have he : caller' = caller := Option.some.inj (hC'.symm.trans hC)
    subst caller'
    have hCVal : ParametricSourceSuccessor.denoteWith f (commonUnits ρ) (caller (UnaryCarrier.headIndex k)) =
        unitValue f (opC.vector 1) := by
      change _ = unitValue f (vC 1)
      rw [hCC]
      exact positiveCommonValue f _ (hg (UnaryCarrier.headIndex k)) (by change 0 < 1; decide) ρ
    rw [hBody,hCVal,hHead μ,← hRecords.2.2]
    simpa only [hCLen,Δ,ops,cs,List.length_map] using hBalance

theorem actualOriginalConstruction : CurrentGroundConstructionTargets.ActualOriginalConstruction := by
  refine ⟨literalTypedConstruction,?_⟩
  intro p f k Γ P C hGen hAct
  obtain ⟨e,rfl⟩ := (TrackedSource.Proof.exactGrammar k (Ty.curriedGround (k+1) :: Γ) .here 0 P).1 hGen
  exact literalTypedConstruction p f k Γ e C
    ((TrackedSource.Proof.exactActivity k (Ty.curriedGround (k+1) :: Γ) .here 0 e).2 hAct)

end LogicLineages.ControlSensitivityCurrent.CurrentGroundConstruction
