module

public import LogicLineages.ComputabilityKnowledge.Comparators.AffineParameterComparison
public import LogicLineages.ComputabilityKnowledge.UnaryComparisonProof

@[expose] public section

/-! External proof of the affine-parameter consumer after exact target freeze.
The original positive valuation is preserved literally; no WW or norm claim
is inferred from this scalar consumer. -/
namespace LogicLineages.ComputabilityKnowledge.AffineParameterComparisonProof

open PositiveExpression CircuitReduction FiniteComparisonEnumeration
open AffineParameterSubstitution AffineParameterComparison

theorem exactValuation : Comparators.AffineParameterComparison.ExactValuation := by
  intro d as bs h n i
  rfl

private theorem holds_transport (weak : Bool) (d : Nat) (as bs : List Nat)
    (h : Admissible d as bs) (a b : Expr (Fin d)) (n : PosNat) :
    UnaryComparison.Holds weak (substitute as bs a) (substitute as bs b) n ↔
      Holds weak d as bs h a b n := by
  have ha := (AffineParameterSubstitutionProof.literalSubstitution d as bs a h).2
    n (valuation d as bs h n) (fun _ => rfl)
  have hb := (AffineParameterSubstitutionProof.literalSubstitution d as bs b h).2
    n (valuation d as bs h n) (fun _ => rfl)
  simp only [UnaryComparison.Holds, Holds, ha, hb]

theorem exactRawDomain : Comparators.AffineParameterComparison.ExactRawDomain := by
  intro weak d as bs a b
  have ha := AffineParameterSubstitutionProof.exactRawDomain d as bs a
  have hb := AffineParameterSubstitutionProof.exactRawDomain d as bs b
  have hr : (resultCode weak d as bs a b).isSome =
      (coefficientsOK d as bs && ((decodeExpr d a).isSome && (decodeExpr d b).isSome)) := by
    cases hca : AffineParameterSubstitution.compileCode d as bs a with
    | none =>
        rw [hca] at ha
        cases hc : coefficientsOK d as bs <;> cases hd : (decodeExpr d a).isSome <;>
          simp_all [resultCode]
    | some a' =>
        cases hcb : AffineParameterSubstitution.compileCode d as bs b with
        | none =>
            rw [hca] at ha
            rw [hcb] at hb
            cases hc : coefficientsOK d as bs <;> cases hd : (decodeExpr d b).isSome <;>
              simp_all [resultCode]
        | some b' =>
            obtain ⟨ea, hea⟩ := AffineParameterSubstitutionProof.outputSourceSyntax d as bs a a' hca
            obtain ⟨eb, heb⟩ := AffineParameterSubstitutionProof.outputSourceSyntax d as bs b b' hcb
            have hda := (ExponentialIdentityProof.rawInputCoverage 1 a').mpr ⟨ea, hea⟩
            have hdb := (ExponentialIdentityProof.rawInputCoverage 1 b').mpr ⟨eb, heb⟩
            have hu := (UnaryComparisonProof.exactRawDomain weak a' b').1
            rw [hca] at ha
            rw [hcb] at hb
            have hab : coefficientsOK d as bs = true ∧
                (decodeExpr d a).isSome = true ∧ (decodeExpr d b).isSome = true := by
              have haa : coefficientsOK d as bs = true ∧ (decodeExpr d a).isSome = true := by simpa using ha.symm
              have hbb : coefficientsOK d as bs = true ∧ (decodeExpr d b).isSome = true := by simpa using hb.symm
              exact ⟨haa.1, haa.2, hbb.2⟩
            simp only [resultCode, hca, hcb, Option.bind_some, bind, Option.bind, hu, hda, hdb,
              hab.1, hab.2.1, hab.2.2, Bool.and_self]
  exact ⟨hr, by simpa [decisionCode] using hr⟩

theorem sourceResult : Comparators.AffineParameterComparison.SourceResult := by
  intro weak d as bs h a b
  have ha := AffineParameterSubstitutionProof.literalCompiler d as bs a h
  have hb := AffineParameterSubstitutionProof.literalCompiler d as bs b h
  have hu := UnaryComparisonProof.sourceResult weak (substitute as bs a) (substitute as bs b)
  simpa only [resultCode, ha, hb, Option.bind_some, bind, Option.bind, holds_transport weak d as bs h a b] using hu

theorem sourceDecision : Comparators.AffineParameterComparison.SourceDecision := by
  intro weak d as bs h a b
  have ha := AffineParameterSubstitutionProof.literalCompiler d as bs a h
  have hb := AffineParameterSubstitutionProof.literalCompiler d as bs b h
  have hu := UnaryComparisonProof.sourceDecision weak (substitute as bs a) (substitute as bs b)
  simpa only [decisionCode, resultCode, ha, hb, Option.bind_some, bind, Option.bind,
    UnaryComparison.decisionCode, holds_transport weak d as bs h a b] using hu

abbrev Input := Bool × Nat × List Nat × List Nat × List Nat × List Nat

private theorem pr_compileA : Primrec (fun p : Input =>
    AffineParameterSubstitution.compileCode p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1) := by
  have hargs : Primrec (fun p : Input => (p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1)) :=
    (Primrec.fst.comp Primrec.snd).pair ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).pair
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))
  exact (AffineParameterSubstitutionProof.pr_compileCode.comp hargs).of_eq (fun _ => rfl)

private theorem pr_compileB : Primrec (fun p : Input =>
    AffineParameterSubstitution.compileCode p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.2) := by
  have hargs : Primrec (fun p : Input => (p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.2)) :=
    (Primrec.fst.comp Primrec.snd).pair ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).pair
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))
  exact (AffineParameterSubstitutionProof.pr_compileCode.comp hargs).of_eq (fun _ => rfl)

private theorem pr_inner : Primrec (fun p : Input × List Nat =>
    (AffineParameterSubstitution.compileCode p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2.2).bind
      (fun b => UnaryComparison.resultCode p.1.1 p.2 b)) := by
  have hargs : Primrec (fun q : (Input × List Nat) × List Nat => (q.1.1.1, q.1.2, q.2)) :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
  have hstep := (UnaryComparisonProof.pr_resultCode.comp hargs).of_eq (fun _ => rfl)
  exact Primrec.option_bind (pr_compileB.comp Primrec.fst) hstep.to₂

theorem pr_resultCode : Primrec (fun p : Input =>
    resultCode p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) :=
  Primrec.option_bind pr_compileA pr_inner.to₂

private theorem pr_isNone : Primrec (Option.isNone : Option Nat → Bool) :=
  ((Primrec.eq.comp Primrec.option_isSome (Primrec.const false)).decide).of_eq (by intro o; cases o <;> rfl)

theorem pr_decisionCode : Primrec (fun p : Input =>
    decisionCode p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) :=
  Primrec.option_map pr_resultCode (pr_isNone.comp Primrec.snd).to₂

theorem actualUniformPrograms : Comparators.AffineParameterComparison.ActualUniformPrograms :=
  ⟨pr_resultCode, pr_decisionCode⟩

theorem affineParameterComparison : Comparators.AffineParameterComparison.Target :=
  ⟨exactValuation, exactRawDomain, sourceResult, sourceDecision, actualUniformPrograms⟩

end LogicLineages.ComputabilityKnowledge.AffineParameterComparisonProof
