module
public import LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.Targets
import LogicLineages.ComputabilityKnowledge.NonnegativePolynomialComparisonEffectivityProof
import LogicLineages.ComputabilityKnowledge.WWBoundedVectorCodeProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.ProgramsProof
open PositiveExpression CircuitReduction

/-- The comparison frame preserves the arity and both original expression codes. -/
theorem unframe_framed (raw : ScalarCode) : unframe (framed raw) = raw := by
  rcases raw with ⟨d, a, b⟩
  simp [unframe, framed, List.take_append_length, List.drop_left]

theorem framed_expressionCode {d : Nat} (a b : Expr (Fin d)) :
    framed (expressionCode a b) =
      CircuitComparison.encodeComparison (d, a.rename Fin.val, b.rename Fin.val) := by
  simp [framed, expressionCode, CircuitComparison.encodeComparison, encodeSystem]

private theorem unframe_comparison (p : Nat × Expr Nat × Expr Nat) :
    unframe (CircuitComparison.encodeComparison p) =
      (p.1, encodeExpr p.2.1, encodeExpr p.2.2) := by
  have hf : CircuitComparison.encodeComparison p =
      framed (p.1, encodeExpr p.2.1, encodeExpr p.2.2) := by
    simp [CircuitComparison.encodeComparison, encodeSystem, framed]
  rw [hf, unframe_framed]

theorem framingProgram : Targets.FramingProgram := by
  have hd : Primrec (fun raw : ScalarCode => raw.1) := Primrec.fst
  have ha : Primrec (fun raw : ScalarCode => raw.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hb : Primrec (fun raw : ScalarCode => raw.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact (Primrec.list_cons.comp hd
    (Primrec.list_cons.comp (Primrec.list_length.comp ha)
      (Primrec.list_cons.comp (Primrec.list_length.comp hb)
        (Primrec.list_append.comp ha hb)))).to_comp

theorem scalarValidation : Targets.ScalarValidation := by
  constructor
  · exact Primrec.option_isSome.to_comp.comp WWBoundedVectorCodeProof.actualUniformProgram
  · intro raw
    exact WWBoundedVectorCodeProof.exactRawDomain raw.1 raw.2.1 raw.2.2

private theorem unframePrimrec : Primrec unframe := by
  have hg (i : Nat) : Primrec (fun xs : List Nat => xs.getD i 0) :=
    (Primrec.list_getD 0).comp Primrec.id (Primrec.const i)
  have hd : Primrec (fun xs : List Nat => xs.drop 3) :=
    Primrec.list_drop.comp (Primrec.const 3) Primrec.id
  exact ((hg 0).pair ((Primrec.list_take.comp (hg 1) hd).pair
    (Primrec.list_drop.comp (hg 1) hd))).of_eq (fun _ => rfl)

private theorem scalarProgramPrimrec (weak : Bool) : Primrec (scalarProgram weak) := by
  have hc : Primrec (if weak then NonnegativePolynomialComparison.weakCode
      else NonnegativePolynomialComparison.strictCode) := by
    cases weak
    · exact NonnegativePolynomialComparisonEffectivityProof.strictPrimrec
    · exact NonnegativePolynomialComparisonEffectivityProof.weakPrimrec
  have hbind := Primrec.option_bind (Primrec.decode (α := List Nat))
    (hc.comp Primrec.snd).to₂
  exact (unframePrimrec.comp
    (Primrec.option_getD.comp hbind (Primrec.const []))).of_eq (fun _ => rfl)

theorem scalarPrograms : Targets.ScalarPrograms := by
  intro weak
  exact (scalarProgramPrimrec weak).to_comp

theorem scalarCalibration : Targets.ScalarCalibration := by
  intro weak p
  cases weak
  · change unframe (((Encodable.decode (Encodable.encode (PolynomialCircuit.encode p)) :
        Option (List Nat)).bind NonnegativePolynomialComparison.strictCode).getD []) = _
    rw [Encodable.encodek]
    change unframe ((NonnegativePolynomialComparison.strictCode
      (PolynomialCircuit.encode p)).getD []) = _
    rw [NonnegativePolynomialComparisonEffectivityProof.strictCorrespondence]
    change unframe (CircuitComparison.encodeComparison
      (NonnegativePolynomialComparison.strictOutput p)) = _
    rw [unframe_comparison]
    rfl
  · change unframe (((Encodable.decode (Encodable.encode (PolynomialCircuit.encode p)) :
        Option (List Nat)).bind NonnegativePolynomialComparison.weakCode).getD []) = _
    rw [Encodable.encodek]
    change unframe ((NonnegativePolynomialComparison.weakCode
      (PolynomialCircuit.encode p)).getD []) = _
    rw [NonnegativePolynomialComparisonEffectivityProof.weakCorrespondence]
    change unframe (CircuitComparison.encodeComparison
      (NonnegativePolynomialComparison.weakOutput p)) = _
    rw [unframe_comparison]
    rfl

theorem vectorPrograms : Targets.VectorPrograms := by
  intro weak
  have hr : Computable (scalarProgram false) := scalarPrograms false
  have hd : Computable (fun e : Nat => (scalarProgram false e).1) :=
    Computable.fst.comp hr
  have ha : Computable (fun e : Nat => (scalarProgram false e).2.1) :=
    Computable.fst.comp (Computable.snd.comp hr)
  have hb : Computable (fun e : Nat => (scalarProgram false e).2.2) :=
    Computable.snd.comp (Computable.snd.comp hr)
  have hpad : Computable (fun e : Nat => WWBoundedVectorCode.paddingCode
      (scalarProgram false e).1 (scalarProgram false e).2.2
      (scalarProgram false e).2.1) :=
    WWBoundedVectorCodeProof.actualUniformProgram.comp (hd.pair (hb.pair ha))
  have hout : Computable (fun e : Nat => (WWBoundedVectorCode.paddingCode
      (scalarProgram false e).1 (scalarProgram false e).2.2
      (scalarProgram false e).2.1).getD ([], [], [])) :=
    Computable.option_getD hpad (Computable.const ([], [], []))
  have hl := Computable.fst.comp hout
  cases weak
  · exact (hd.pair (hl.pair (Computable.snd.comp
      (Computable.snd.comp hout)))).of_eq (fun _ => rfl)
  · exact (hd.pair (hl.pair (Computable.fst.comp
      (Computable.snd.comp hout)))).of_eq (fun _ => rfl)

theorem vectorCalibration : Targets.VectorCalibration := by
  intro weak e d u v hu hv hs
  simp only [vectorProgram, hs, expressionCode,
    WWBoundedVectorCodeProof.literalConstruction d u v hu hv, Option.getD_some]
  cases weak <;> rfl

end LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.ProgramsProof
