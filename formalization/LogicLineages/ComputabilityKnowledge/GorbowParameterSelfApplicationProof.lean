module

public import LogicLineages.ComputabilityKnowledge.GorbowParameterSelfApplicationTargets
public import LogicLineages.ComputabilityKnowledge.GorbowSubstitutionCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaCompositionProof
public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructorsProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedSyntaxCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

@[expose] public section
/-! Retained-parameter self-application Formula2 → Formula1. The single open
formula openSelf(phi) has, by exact AST composition, the closed instances
closedSelf(phi,u). The raw algorithm is the unchanged context-2→0 substitution
codec with the two literal numeral codes, calibrated to the actual sorted
codes, primitive recursive, and realized by one fixed arity-two program.
This is syntax only: no CK equivalence or fixed point is asserted. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowParameterSelfApplication.Proof
open GorbowSyntax GorbowSortedSyntaxCode

/-! ### Exact AST commutation -/

private theorem substituteNumeral {m n : Nat} (σ : Fin m → Term n) (k : Nat) :
    GorbowSubstitution.substitute σ (Term.numeral k) = Term.numeral k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg Term.succ ih

theorem literalCommutation : GorbowParameterSelfApplication.Targets.LiteralCommutation := by
  intro phi u
  unfold GorbowStandardInstances.instantiate openSelf closedSelf
  rw [GorbowFormulaCompositionProof.composition]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => exact substituteNumeral _ (formulaCode phi)
  | succ j => rfl

/-! ### Raw and sorted calibration -/

private theorem rawDictionary (phi : Formula 2) (u : Nat) :
    GorbowLiftedDictionary.dictionary (closedDictionary phi u) =
      [GorbowCodeConstructors.numeral (formulaRawNumber (GorbowFormulaPrefixCode.encode phi)),
        GorbowCodeConstructors.numeral u] := by
  have h0 : GorbowTermPrefixCode.encode (closedDictionary phi u 0) =
      GorbowCodeConstructors.numeral (formulaRawNumber (GorbowFormulaPrefixCode.encode phi)) :=
    GorbowCodeConstructorsProof.numeralCalibration 0 (formulaCode phi)
  have h1 : ∀ j : Fin 1, GorbowTermPrefixCode.encode (closedDictionary phi u j.succ) =
      GorbowCodeConstructors.numeral u :=
    fun _ => GorbowCodeConstructorsProof.numeralCalibration 0 u
  unfold GorbowLiftedDictionary.dictionary
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  exact congrArg₂ List.cons h0 (congrArg₂ List.cons (h1 0) rfl)

private theorem encodedSelf (phi : Formula 2) (u : Nat) :
    rawParameterSelf (GorbowFormulaPrefixCode.encode phi) u =
      some (GorbowFormulaPrefixCode.encode (closedSelf phi u)) := by
  unfold rawParameterSelf
  apply (GorbowSubstitutionCodeProof.exactOutput.2 2 0 _ _ _).mpr
  exact ⟨closedDictionary phi u, phi, (rawDictionary phi u).symm, rfl, rfl⟩

theorem numericCalibration : GorbowParameterSelfApplication.Targets.NumericCalibration := by
  intro phi u
  have hd := GorbowSortedSyntaxCodeProof.actualCalibration.2.1 2 phi
  unfold numeric
  rw [hd]
  change (rawParameterSelf (GorbowFormulaPrefixCode.encode phi) u).bind
    (fun out => some (formulaRawNumber out)) = some (formulaCode (closedSelf phi u))
  rw [encodedSelf]
  rfl

theorem numericExact : GorbowParameterSelfApplication.Targets.NumericExact := by
  intro code u out
  constructor
  · intro h
    cases hd : decodeFormulaRaw code with
    | none => simp [numeric, hd] at h
    | some raw =>
      cases hs : rawParameterSelf raw u with
      | none => simp [numeric, hd, hs] at h
      | some rawOut =>
        obtain ⟨_, phi, _, hr, _⟩ :=
          (GorbowSubstitutionCodeProof.exactOutput.2 2 0 _ raw rawOut).mp hs
        subst raw
        have hc : code = formulaCode phi :=
          (GorbowSortedSyntaxCodeProof.exactRawDecoding.1 _ _).mp hd
        subst code
        rw [numericCalibration] at h
        exact ⟨phi, rfl, (Option.some.inj h).symm⟩
  · rintro ⟨phi, rfl, rfl⟩
    exact numericCalibration phi u

/-! ### Primitive recursion -/

private theorem pr_raw : Primrec (fun x : List Nat × Nat => rawParameterSelf x.1 x.2) := by
  have hn := GorbowCodeConstructorsProof.uniformPrograms.2.2.2.1
  have hf := GorbowSortedSyntaxCodeProof.uniformPrograms.2.2.1
  have hd : Primrec (fun x : List Nat × Nat =>
      [GorbowCodeConstructors.numeral (formulaRawNumber x.1), GorbowCodeConstructors.numeral x.2]) :=
    Primrec.list_cons.comp (hn.comp (hf.comp Primrec.fst))
      (Primrec.list_cons.comp (hn.comp Primrec.snd) (Primrec.const []))
  exact GorbowSubstitutionCodeProof.uniformPrograms.2.2.2.2.comp
    ((Primrec.const 2).pair ((Primrec.const 0).pair (hd.pair Primrec.fst)))

private theorem pr_map : Primrec (fun x : List Nat × Nat =>
    (rawParameterSelf x.1 x.2).map formulaRawNumber) :=
  Primrec.option_map pr_raw (GorbowSortedSyntaxCodeProof.uniformPrograms.2.2.1.comp Primrec.snd).to₂

private theorem pr_numeric : Primrec (fun x : Nat × Nat => numeric x.1 x.2) := by
  have h := Primrec.option_bind
    (GorbowSortedSyntaxCodeProof.uniformPrograms.2.2.2.2.2.1.comp Primrec.fst)
    (pr_map.comp (Primrec.snd.pair (Primrec.snd.comp Primrec.fst))).to₂
  exact h.of_eq (fun x => by
    cases hd : decodeFormulaRaw x.1 <;> simp [numeric, hd]
    case some raw => cases rawParameterSelf raw x.2 <;> rfl)

theorem uniformPrograms : GorbowParameterSelfApplication.Targets.UniformPrograms :=
  ⟨pr_raw, pr_numeric⟩

/-! ### A fixed arity-two program -/

theorem programWitness : GorbowParameterSelfApplication.Targets.ProgramWitness := by
  have hg : Primrec (fun v : List.Vector Nat 2 => (numeric (v.get 0) (v.get 1)).getD 0) :=
    Primrec.option_getD.comp
      (pr_numeric.comp ((Primrec.vector_get.comp Primrec.id (Primrec.const (0 : Fin 2))).pair
        (Primrec.vector_get.comp Primrec.id (Primrec.const (1 : Fin 2)))))
      (Primrec.const 0)
  obtain ⟨p, hp⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 2 _ hg
  exact ⟨p, fun code u => hp _⟩

theorem fullTarget : GorbowParameterSelfApplication.Targets.Target :=
  ⟨literalCommutation, numericCalibration, numericExact, uniformPrograms, programWitness⟩

end LogicLineages.ComputabilityKnowledge.GorbowParameterSelfApplication.Proof
