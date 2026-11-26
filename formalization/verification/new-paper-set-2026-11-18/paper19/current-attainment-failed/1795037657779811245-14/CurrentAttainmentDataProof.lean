module
public import LogicLineages.ControlSensitivityCurrent.CurrentAttainmentTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentOrdinalEvaluationProof
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeCodeProof
public import LogicLineages.ControlSensitivityCurrent.SourceASTObservationProof
public import LogicLineages.StandardControlCurrent.PolicyAssignmentStatementChecks
public import LogicLineages.OrdinalComparison.GeneralOmegaHeadLimitProof
public import LogicLineages.OrdinalComparison.HeadCompleteCountProof
public import LogicLineages.OrdinalComparison.ParametricActualCollapseRecursionProof
public import LogicLineages.OrdinalComparison.EncodedDescentProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentAttainment

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
open GroundEquivalence ExistentialPlan ParametricSourceSuccessor AdmissibleAssignment
open CurrentOrdinalEvaluation (omegaCode)
open ForwardTranslation

theorem standard_growth : FullAddition.Targets.SourceGrowth Phi :=
  ⟨fun _ => le_rfl, Phi_double_tower_gap⟩

theorem closed_note (f : Nat → Nat) (hf : FullAddition.Targets.SourceGrowth f)
    (e : OrdinalExpression []) :
    ∃ a : NONote, CurrentOrdinalEvaluation.evaluate f [] (OrdinalSyntax.typedCode e) =
      rawNoteEncode a.1 ∧ a.1.repr = denoteWith f (fun _ => 1) e := by
  have empty (x : OrdinalComponent []) : False := by
    rcases x with ⟨_, v, _⟩
    cases v
  exact CurrentOrdinalEvaluation.calibration f hf _ OrdinalSyntax.componentCode e [] (fun _ => 1)
    (fun x => (empty x).elim)

theorem encoded_norm (a : NONote) :
    rawNormCode (rawNoteEncode a.1) = actualOrdinalNorm a.1.repr := by
  rw [rawNormCodeCorrect, actualOrdinalNorm_notationCorrespondence a]

private theorem application_scalar (p : AdmissibleSum.Policy) {Γ}
    (v : OrdinalVector Γ 1) (a : OrdinalVector Γ 0) :
    application (σ := .ground) (τ := .ground) p v a 0 =
      .collapse (v 1) (.add (v 0) (a 0)) := by
  change (.collapse (ordinalBoxPositive 0 (ordinalVectorAt v) (ordinalVectorAt a) 1)
    (.add (v 0) (a 0)) : OrdinalExpression Γ) = _
  congr 1
  simp [ordinalBoxPositive, ordinalVectorAt]

private theorem application_ray (p : AdmissibleSum.Policy) (h : Unary)
    (v : OrdinalVector [] 1) (hv : assignment p h.term = some v)
    (c : Nat) (a : Ordinal) (hc : denoteWith Phi (fun _ => 1) (v 0) = (c : Ordinal))
    (ha : denoteWith Phi (fun _ => 1) (v 1) = a)
    (l : NONote) (hl : l.1.repr = ordinalNaturalProduct Ordinal.omega0 a)
    (hlimit : Order.IsSuccLimit l.1.repr) (n : Nat) :
    SourceAST.callValue p Phi h n = actualHeadValue l.1.repr (actualOrdinalNorm l.1.repr+c+1+n)-1 := by
  let Γ := [Ty.ground]
  let r := BooleanCompiler.emptyRename Γ
  let w := SourceRenaming.renameVector r v
  let x : Variable Γ .ground := .here
  let xv : OrdinalVector Γ 0 := fun j => .var ⟨.ground,x,j⟩
  let ρ : Variable Γ .ground → Nat := extend (fun z : Variable [] .ground => nomatch z) n
  let u : OrdinalVector Γ 0 := application (σ := .ground) (τ := .ground) p w xv
  have hw : assignment p (h.term.rename r) = some w := by
    rw [SourceRenaming.Proof.assignmentNaturality, hv]
    rfl
  have hu : assignment p (BooleanCompiler.call h x).term = some u := by
    rw [SourceAST.call_term]
    change (assignment p (h.term.rename r)).bind (fun f =>
      (assignment p (.var x)).bind (fun g => some (application p f g))) = some u
    rw [hw]
    rfl
  let ν : OrdinalComponent Γ → Ordinal := fun z => ((inputs ρ z+1 : Nat) : Ordinal)
  have rename_value (j : Fin 2) : denoteWith Phi ν (w j) = denoteWith Phi (fun _ => 1) (v j) :=
    PolicyObservation.expressionNaturality Phi [] Γ r _ ν (fun _ z _ => nomatch z) _
  let t := actualOrdinalNorm l.1.repr + c + 1 + n
  have ht : actualOrdinalNorm l.1.repr ≤ t := by dsimp [t]; omega
  have hbelow := (actualHeadInputFacts l.1.repr (normalRepresentationSound l) hlimit t ht).1
  have hscalar : denoteWith Phi ν (u 0) = (actualHeadValue l.1.repr t : Ordinal) := by
    rw [application_scalar]
    change ((ParametricActualCollapse.collapseWith Phi (ordinalNaturalSum
      (ordinalNaturalProduct Ordinal.omega0 (denoteWith Phi ν (w 1)))
      (ordinalNaturalSum (denoteWith Phi ν (w 0)) ((n+1 : Nat) : Ordinal))) : Nat) : Ordinal) = _
    rw [rename_value 1, rename_value 0, ha, hc, ← hl, naturalSum_finite, actualNaturalSumFiniteRight]
    have e : c+(n+1) = t - actualOrdinalNorm l.1.repr := by dsimp [t]; omega
    rw [e]
    exact congrArg (fun z : Nat => (z : Ordinal))
      (ParametricActualCollapse.Proof.exactPhiSpecialization (actualHeadInitial l.1.repr t) hbelow)
  have hraw := PolicyOrderWrapper.raw_of_scalar p Phi (inputs ρ) (BooleanCompiler.call h x).term
    (actualHeadValue l.1.repr t) ⟨u, hu, hscalar⟩
  change PolicyCollision.rawScalar p Phi (inputs ρ) (BooleanCompiler.call h x).term - 1 = _
  rw [hraw]

theorem suppliedData : CurrentAttainmentTargets.SuppliedData := by
  intro p h
  let code := RawSourceDAG.encode ⟨[],.arrow .ground .ground,h⟩
  obtain ⟨v, hv, he, hg⟩ := PolicyAssignmentStatementChecks.full.2.2.1 p [] (.arrow .ground .ground) h.term
  obtain ⟨c, hc⟩ := (GenericScalar.generatedPositiveFinite Phi [] (fun _ => 0) _ _ (hg 0)).2 rfl
  let a := denoteWith Phi (fun _ => 1) (v 1)
  have ha : 0 < a := (GenericScalar.generatedPositiveFinite Phi [] (fun _ => 0) _ _ (hg 1)).1
  have hal : a < epsilonZero := GenericScalar.belowEpsilon Phi [] (fun _ => 0) (v 1)
  obtain ⟨an, han, har⟩ := closed_note Phi standard_growth (v 1)
  obtain ⟨cn, hcn, hcr⟩ := closed_note Phi standard_growth (v 0)
  let w := ClosedPositive.omega.evaluate
  have wh : w.1.repr = Ordinal.omega0 := by simp [w, ClosedPositive.evaluate, ONote.repr]
  obtain ⟨hnf, hprod, _⟩ := encodedNaturalProductSourceCorrect w an
  let l : NONote := ⟨_,hnf⟩
  have hl : l.1.repr = ordinalNaturalProduct Ordinal.omega0 a := by
    exact hprod.trans (congrArg₂ ordinalNaturalProduct wh har)
  have hlimit : Order.IsSuccLimit l.1.repr := by
    rw [hl]
    exact (GeneralOmegaHeadLimit.Proof.generalPositiveLimit a ha hal).2.1
  have hs : digits p code = OrdinalSyntax.vectorCode v := by
    unfold digits
    rw [CurrentTreeCode.exactExpansion [] (.arrow .ground .ground) h, he]
    rfl
  have h0 : (digits p code).getD 0 0 = OrdinalSyntax.typedCode (v 0) := by
    rw [hs]
    rfl
  have h1 : (digits p code).getD 1 0 = OrdinalSyntax.typedCode (v 1) := by
    rw [hs]
    rfl
  have hhead : headCode p code = rawNoteEncode l.1 := by
    unfold headCode
    rw [h1, han]
    exact (rawNoteEncodeDecode _).symm
  have hfinite : encodedFiniteValue (rawNoteEncode cn.1) = c := by
    have heq : cn.1.repr = (c : Ordinal) := hcr.trans hc
    have hft := (encodedFiniteCorrect cn).1.mpr (heq.symm ▸ Ordinal.natCast_lt_omega0 c)
    have hf := (encodedFiniteCorrect cn).2 hft
    rw [heq] at hf
    exact_mod_cast hf
  refine ⟨v,c,a,l,hv,hc,rfl,hl,hlimit,?_,hhead,?_⟩
  · unfold offset
    rw [hhead, encoded_norm, h0, hcn, hfinite]
  · exact application_ray p h v hv c a hc rfl l hl hlimit

end LogicLineages.ControlSensitivityCurrent.CurrentAttainment
