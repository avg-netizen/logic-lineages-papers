module
public import LogicLineages.ControlSensitivityCurrent.CurrentControlHardnessLowerProof
public import LogicLineages.ControlSensitivityCurrent.CurrentCounterBoundProof
public import LogicLineages.OrdinalComparison.SourceRestrictedSyntaxCheckerProof
public import LogicLineages.OrdinalComparison.SourceBlankHaltingUniversalityProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentControlHardness

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open ExistentialPlan
open OriginalInput (Query context decode)

private theorem ground_compare (strict : Bool) (p : AdmissibleSum.Policy) (f : Nat → Nat)
    {Γ : List Ty} (a b : OriginalTerm Γ .ground)
    (ρ : Variable Γ .ground → Nat) (av bv : OrdinalVector Γ 0)
    (ha : AdmissibleAssignment.assignment p a = some av)
    (hb : AdmissibleAssignment.assignment p b = some bv) :
    CurrentCounterBound.compareAt f strict av bv (fun c => inputs ρ c + 1) ↔
      if strict then PolicyCollision.rawScalar p f (inputs ρ) a < PolicyCollision.rawScalar p f (inputs ρ) b
      else PolicyCollision.rawScalar p f (inputs ρ) a ≤ PolicyCollision.rawScalar p f (inputs ρ) b := by
  obtain ⟨ca, va, na, _, hva, _⟩ := GenericScalar.actualSourceTotality p f Γ (inputs ρ) a
  obtain ⟨cb, vb, nb, _, hvb, _⟩ := GenericScalar.actualSourceTotality p f Γ (inputs ρ) b
  have la : AdmissibleAssignment.assignment p a = some ca := va
  have lb : AdmissibleAssignment.assignment p b = some cb := vb
  rw [ha] at la
  rw [hb] at lb
  cases Option.some.inj la
  cases Option.some.inj lb
  have ra := PolicyOrderWrapper.raw_of_scalar p f (inputs ρ) a _ ⟨_, ha, hva⟩
  have rb := PolicyOrderWrapper.raw_of_scalar p f (inputs ρ) b _ ⟨_, hb, hvb⟩
  unfold CurrentCounterBound.compareAt
  have hpos : ∀ j : Nat, CurrentCounterBound.coordinate f av (fun c => inputs ρ c + 1) (j+1) ≤
      CurrentCounterBound.coordinate f bv (fun c => inputs ρ c + 1) (j+1) := by
    intro j
    simp only [CurrentCounterBound.coordinate, ordinalVectorAt, dif_neg (show ¬ j+1 < 0+1 by omega)]
  rw [and_iff_right hpos]
  change (if strict then
    ParametricSourceSuccessor.denoteWith f _ (av 0) < ParametricSourceSuccessor.denoteWith f _ (bv 0)
    else ParametricSourceSuccessor.denoteWith f _ (av 0) ≤ ParametricSourceSuccessor.denoteWith f _ (bv 0)) ↔ _
  rw [hva, hvb, ra, rb]
  cases strict <;> simp

private theorem good_ground (strict : Bool) (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (n : Nat) (a b : OriginalTerm (List.replicate n Ty.ground) .ground) :
    CurrentCounterBound.Good p f (n, strict, SyntaxCode.encodeTerm a, SyntaxCode.encodeTerm b) ↔
      queryHolds strict p f a b := by
  let Γ := List.replicate n Ty.ground
  let q : Query := (n, strict, SyntaxCode.encodeTerm a, SyntaxCode.encodeTerm b)
  change CurrentCounterBound.Good p f q ↔ queryHolds strict p f a b
  have apply_mode : queryHolds strict p f a b ↔ ∀ ρ : Variable Γ .ground → Nat,
      if strict then PolicyCollision.rawScalar p f (inputs ρ) a < PolicyCollision.rawScalar p f (inputs ρ) b
      else PolicyCollision.rawScalar p f (inputs ρ) a ≤ PolicyCollision.rawScalar p f (inputs ρ) b := by
    cases strict <;> exact Iff.rfl
  rw [apply_mode]
  constructor
  · intro h ρ
    obtain ⟨av, ha, _⟩ := PolicyAssignmentStatementChecks.full.2.2.1 p Γ .ground a
    obtain ⟨bv, hb, _⟩ := PolicyAssignmentStatementChecks.full.2.2.1 p Γ .ground b
    exact (ground_compare strict p f a b ρ av bv ha hb).mp
      (h .ground .ground a b av bv rfl rfl ha hb _ (fun _ => Nat.zero_lt_succ _))
  · intro h τ υ l r lv rv hl hr hla hra ν hν
    change SyntaxCode.encodeTerm l = SyntaxCode.encodeTerm a at hl
    change SyntaxCode.encodeTerm r = SyntaxCode.encodeTerm b at hr
    have ht := SourceTypedCodeAdequacy.Proof.fixedContextTypeUniqueness Γ τ .ground l a
      (SyntaxCode.Proof.codeInjective hl)
    have hu := SourceTypedCodeAdequacy.Proof.fixedContextTypeUniqueness Γ υ .ground r b
      (SyntaxCode.Proof.codeInjective hr)
    cases ht
    cases hu
    have he := SourceTypedCodeAdequacy.Proof.typedCodeInjective Γ .ground hl
    have hh := SourceTypedCodeAdequacy.Proof.typedCodeInjective Γ .ground hr
    cases he
    cases hh
    obtain ⟨ρ, hρ, _⟩ :=
      (SourceMachineRawValuations.Proof.positiveCoordinateEquivalence Γ (CurrentCounterBound.ground_context q)).2 ν hν
    rw [funext hρ]
    exact (ground_compare strict p f l r ρ lv rv hla hra).mpr (h ρ)

private def asGeneralQuery (strict : Bool) (n : Nat) : Nat :=
  match SourceMachineQueryCode.unpack n with
  | none => Encodable.encode ((0, strict, 7, 7) : Query)
  | some (arity, l, r) => Encodable.encode ((arity, strict, l, r) : Query)

private theorem general_computable (strict : Bool) : Computable (asGeneralQuery strict) := by
  have pack : Primrec (fun x : Nat × SourceMachineQueryCode.Query =>
      Encodable.encode ((x.2.1, strict, x.2.2.1, x.2.2.2) : Query)) :=
    Primrec.encode.comp ((Primrec.fst.comp Primrec.snd).pair
      ((Primrec.const strict).pair (Primrec.snd.comp Primrec.snd)))
  apply (Computable.option_casesOn SourceMachineQueryCode.Proof.unpack_primitive.to_comp
    (Computable.const (Encodable.encode ((0, strict, 7, 7) : Query))) pack.to_comp.to₂).of_eq
  intro n
  cases SourceMachineQueryCode.unpack n <;> rfl

private theorem good_restricted (strict : Bool) (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (n : Nat) (hn : SourceGammaRestrictedReduction.RestrictedSyntax n) :
    CurrentCounterBound.codedGood p f (asGeneralQuery strict n) ↔ rawMember strict p f n := by
  obtain ⟨m, l, r, hcode, _⟩ := hn
  have hpack : n = SourceMachineQueryCode.pack (m, SyntaxCode.encodeTerm l, SyntaxCode.encodeTerm r) := by
    exact Encodable.encode_of_decode hcode |>.symm
  rw [CurrentCounterBound.codedGood, asGeneralQuery, hcode]
  change CurrentCounterBound.Good p f
    (decode (Encodable.encode ((m, strict, SyntaxCode.encodeTerm l, SyntaxCode.encodeTerm r) : Query))) ↔ _
  rw [OriginalInput.originalInputCodecCorrect.1, good_ground, hpack, raw_canonical]

private theorem upper (b : Nat) (p : AdmissibleSum.Policy) (hp : PolicyShape.Effective p) (strict : Bool) :
    REPred (fun n => ¬ member strict p b n) := by
  let f := SourceMachineControlNonperiodicity.gamma b
  have hf := CurrentMachinePlan.gamma_growth b
  have hc : Computable f := (ActualMachine.actualMachineGrowth b).2.1.to_comp
  have hgood := (CurrentCounterBound.full p hp f hc hf).1
  let check := SourceRestrictedSyntaxChecker.restrictedCode
  have hcheck : Computable check := SourceRestrictedSyntaxChecker.Proof.uniformPrimitiveRecursive.2.2.to_comp
  have hr := Partrec.comp hgood (general_computable strict)
  have hpart := Partrec.cond hcheck hr ((Computable.const () : Computable (fun _ : Nat => ())).partrec)
  apply hpart.dom_re.of_eq
  intro n
  change (cond (check n) (Part.assert (¬ CurrentCounterBound.codedGood p f (asGeneralQuery strict n))
    (fun _ => Part.some ())) (Part.some ())).Dom ↔ _
  cases hcheckn : check n
  · have hn : ¬ SourceGammaRestrictedReduction.RestrictedSyntax n := fun h =>
      Bool.noConfusion (hcheckn.symm.trans ((SourceRestrictedSyntaxChecker.Proof.exactSyntaxClass n).mpr h))
    simp [hcheckn, member, hn]
  · have hn := (SourceRestrictedSyntaxChecker.Proof.exactSyntaxClass n).mp hcheckn
    simp [hcheckn, Part.assert, member, hn, good_restricted strict p f n hn]

theorem completeness : CurrentControlHardnessTargets.Completeness := by
  intro b p hp strict
  refine ⟨upper b p hp strict, ?_⟩
  intro P hP
  obtain ⟨⟨f, hp, he⟩, _⟩ := SourceBlankHaltingUniversality.Proof.reUniversality (fun n => ¬ P n) hP
  have first : ManyOneReducible P (fun e => ¬ SourceBlankMachineSimulation.Halts e) := by
    refine ⟨f, hp.to_comp, fun n => ?_⟩
    classical
    exact not_not.symm.trans (not_congr (he n))
  have second : ManyOneReducible (fun e => ¬ SourceBlankMachineSimulation.Halts e) (member strict p b) := by
    have h := exactLowering b p strict
    exact ⟨output strict b, h.1.to_comp, fun e => (h.2 e).2.2.symm⟩
  exact first.trans second

end LogicLineages.ControlSensitivityCurrent.CurrentControlHardness
