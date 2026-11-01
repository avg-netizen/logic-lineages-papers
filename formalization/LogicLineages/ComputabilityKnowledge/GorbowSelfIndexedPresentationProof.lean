module

public import LogicLineages.ComputabilityKnowledge.GorbowSelfIndexedPresentationTargets
public import LogicLineages.ComputabilityKnowledge.GorbowInstanceCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructorsProof
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaPrefixCodeProof

@[expose] public section
/-! Actual syntactic self-indexing via the paid literal instance compiler and
Kleene's standard recursion theorem. No predicate claiming to have its own
index is postulated; the ordinary code is constructed by the theorem. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowSelfIndexedPresentation.Proof
open GorbowSyntax

theorem literalInstance : Targets.LiteralInstance := by
  intro template c
  unfold instanceRaw
  apply (GorbowInstanceCodeProof.exactInstance 0 _ _ _).mpr
  exact ⟨template, Term.numeral (Encodable.encode c), rfl,
    (GorbowCodeConstructorsProof.numeralCalibration 0 (Encodable.encode c)).symm, rfl⟩

private theorem pr_instance (template : Formula 1) : Primrec (instanceRaw template) := by
  have hn : Primrec (fun c : Code => GorbowCodeConstructors.numeral (Encodable.encode c)) :=
    GorbowCodeConstructorsProof.uniformPrograms.2.2.2.1.comp Primrec.encode
  have hi : Primrec (fun c : Code =>
      ((0 : Nat), GorbowFormulaPrefixCode.encode template,
        GorbowCodeConstructors.numeral (Encodable.encode c))) :=
    (Primrec.const 0).pair ((Primrec.const _).pair hn)
  have h := GorbowInstanceCodeProof.uniformPrograms.2.1.comp hi
  exact h.of_eq (fun _ => rfl)

private theorem finiteMembership (codes : List (List Nat)) :
    Primrec (fun raw : List Nat => decide (raw ∈ codes)) := by
  induction codes with
  | nil => simpa using (Primrec.const false : Primrec (fun _ : List Nat => false))
  | cons code codes ih =>
    have h := Primrec.or.comp
      (Primrec.eq.comp (Primrec.id : Primrec (fun raw : List Nat => raw))
        (Primrec.const code)).decide ih
    exact h.of_eq (fun raw => by simp; rfl)

theorem uniformRawChecker : Targets.UniformRawChecker := by
  intro base template
  have hb : Primrec (fun p : Code × List Nat =>
      decide (p.2 ∈ base.map GorbowFormulaPrefixCode.encode)) :=
    (finiteMembership _).comp Primrec.snd
  have hd : Primrec (fun p : Code × List Nat => (instanceRaw template p.1).getD []) :=
    Primrec.option_getD.comp ((pr_instance template).comp Primrec.fst) (Primrec.const [])
  have he := (Primrec.eq.comp Primrec.snd hd).decide
  have h := Primrec.or.comp hb he
  exact h.of_eq (fun p => by simp [check, axiomCodes])

private theorem pr_numericDecode : Primrec (fun p : Code × Nat =>
    Encodable.decode (α := List Nat) p.2) := Primrec.decode.comp Primrec.snd

private theorem pr_numericSome (base : List Sentence) (template : Formula 1) :
    Primrec (fun z : (Code × Nat) × List Nat =>
      if check base template z.1.1 z.2 then 1 else 0) := by
  have hi : Primrec (fun z : (Code × Nat) × List Nat => (z.1.1, z.2)) :=
    (Primrec.fst.comp Primrec.fst).pair Primrec.snd
  have h := (uniformRawChecker base template).comp hi
  have hc : Primrec (fun z : (Code × Nat) × List Nat => check base template z.1.1 z.2) :=
    h.of_eq (fun _ => rfl)
  have hs := Primrec.cond hc (Primrec.const 1) (Primrec.const 0)
  exact hs.of_eq (fun z => by cases hc : check base template z.1.1 z.2 <;> rfl)

theorem uniformNumericChecker : Targets.UniformNumericChecker := by
  intro base template
  have h := Primrec.option_casesOn pr_numericDecode (Primrec.const 0)
    (pr_numericSome base template).to₂
  exact h.of_eq (fun p => by
    unfold numericCheck
    cases he : Encodable.decode (α := List Nat) p.2 <;> rfl)

theorem actualFixedPoint : Targets.ActualFixedPoint := by
  intro base template
  have hf : Partrec₂ (fun c input => Part.some (numericCheck base template c input)) :=
    (uniformNumericChecker base template).to_comp
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.fixed_point₂ hf
  exact ⟨c, fun input => congrFun hc input⟩

private theorem codesCorrect (base : List Sentence) (template : Formula 1) (c : Code) :
    axiomCodes base template c = (axioms base template c).map GorbowFormulaPrefixCode.encode := by
  rw [axiomCodes, literalInstance template c]
  simp only [Option.getD_some, axioms, List.map_append, List.map_cons, List.map_nil]

private theorem checkExact (base : List Sentence) (template : Formula 1) (c : Code)
    (sigma : Sentence) : check base template c (GorbowFormulaPrefixCode.encode sigma) = true ↔
      Theory base template c sigma := by
  unfold check Theory
  rw [decide_eq_true_eq, codesCorrect]
  constructor
  · intro h
    obtain ⟨tau, ht, he⟩ := List.mem_map.mp h
    have eqs := GorbowFormulaPrefixCodeProof.encodingInjective 0 he
    simpa only [eqs] using ht
  · intro h
    exact List.mem_map.mpr ⟨sigma, h, rfl⟩

theorem exactPresentedTheory : Targets.ExactPresentedTheory := by
  intro base template
  obtain ⟨c, hc⟩ := actualFixedPoint base template
  refine ⟨c, hc, ?_, ?_⟩
  · funext sigma
    apply propext
    change (1 ∈ c.eval (Encodable.encode (GorbowFormulaPrefixCode.encode sigma))) ↔ _
    rw [hc]
    have he := checkExact base template c sigma
    cases hb : check base template c (GorbowFormulaPrefixCode.encode sigma) <;>
      simp [numericCheck, hb] at he ⊢ <;> exact he
  · funext sigma
    apply propext
    exact checkExact base template c sigma

theorem fullTarget : Targets.Target :=
  ⟨literalInstance, uniformRawChecker, uniformNumericChecker, actualFixedPoint,
    exactPresentedTheory⟩

end LogicLineages.ComputabilityKnowledge.GorbowSelfIndexedPresentation.Proof
