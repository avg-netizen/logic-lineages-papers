module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowAtomicSchemaCode
public import LogicLineages.ComputabilityKnowledge.GorbowAtomicParameterCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowAtomicAnnotationProof
public import LogicLineages.ComputabilityKnowledge.GorbowSubstitutionCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowAtomicTruthProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowAtomicSchemaCodeProof
open GorbowSyntax GorbowNameDictionary GorbowRevisionComposition GorbowAtomicTruth
open GorbowAtomicSchemaCode GorbowCodeConstructors GorbowAtomicParameterCode

private theorem substitutionAt (n m : Nat) (R : Formula m) (names : Fin n → Fin m) :
    GorbowSubstitutionCode.substituteFormulaCode m n (valueSlots m (namesList names))
      (GorbowFormulaPrefixCode.encode R)=some (GorbowFormulaPrefixCode.encode
        (GorbowFormulaSubstitution.substituteFormula (GorbowAtomicParameters.valueDictionary names) R)) := by
  apply (GorbowSubstitutionCodeProof.exactOutput.2 m n _ _ _).mpr
  exact ⟨GorbowAtomicParameters.valueDictionary names,R,
    (GorbowAtomicParameterCodeProof.dictionaryCalibration n m names).2,rfl,rfl⟩

theorem bodyCalibration : Comparators.GorbowAtomicSchemaCode.BodyCalibration := by
  intro n m R names
  have hl : (namesList names).length=n := by simp [namesList]
  unfold bodyRaw
  rw [hl,substitutionAt]
  change some (binary 8
    (binary 7 (unary 5 (instanceRaw m (GorbowFormulaPrefixCode.encode R) (namesList names))) _)
    (binary 7 _ (unary 5 (instanceRaw m (GorbowFormulaPrefixCode.encode R) (namesList names)))))=_
  rw [GorbowAtomicParameterCodeProof.instanceCalibration n m R names]
  rfl

theorem originalCalibration : Comparators.GorbowAtomicSchemaCode.OriginalCalibration := by
  intro n m R names ha hi hc
  have hg := GorbowAtomicAnnotationProof.originalCalibration n m R names hi hc ha
  have hl : (namesList names).length=n := by simp [namesList]
  unfold compileRaw
  rw [hg]
  simp only [Bool.true_eq,ite_true]
  rw [bodyCalibration,Option.map_some,hl,GorbowRegistryTermCodeProof.closureCalibration]
  rfl

theorem exactRaw : Comparators.GorbowAtomicSchemaCode.ExactRaw := by
  intro m raw ns out
  constructor
  · intro h
    have hg : GorbowAtomicAnnotation.valid m raw ns=true := by
      cases he : GorbowAtomicAnnotation.valid m raw ns with
      | false => simp [compileRaw,he] at h
      | true => rfl
    obtain ⟨R,names,hr,hn,hi,hc,ha⟩ := (GorbowAtomicAnnotationProof.exactDomain m raw ns).mp hg
    have hx := originalCalibration ns.length m R names ha hi hc
    rw [← hr,← hn] at hx
    rw [hx] at h
    exact ⟨R,names,hr,hn,ha,hi,hc,(Option.some.inj h).symm⟩
  · rintro ⟨R,names,hr,hn,ha,hi,hc,ho⟩
    have hx := originalCalibration ns.length m R names ha hi hc
    rw [← hr,← hn,← ho] at hx
    exact hx

theorem exactNumeric : Comparators.GorbowAtomicSchemaCode.ExactNumeric := by
  intro m raw ns out
  constructor
  · intro h
    cases he : compileRaw m raw ns with
    | none => simp [compileNumber,he] at h
    | some code =>
      obtain ⟨R,names,hr,hn,ha,hi,hc,hcode⟩ := (exactRaw m raw ns code).mp he
      have hh : GorbowSortedSyntaxCode.formulaRawNumber code=out := by
        simpa only [compileNumber,he,Option.map_some,Option.some.injEq] using h
      exact ⟨R,names,hr,hn,ha,hi,hc,hh.symm.trans (by rw [hcode];rfl)⟩
  · rintro ⟨R,names,hr,hn,ha,hi,hc,ho⟩
    have he := (exactRaw m raw ns _).mpr ⟨R,names,hr,hn,ha,hi,hc,rfl⟩
    rw [compileNumber,he,Option.map_some,ho]
    rfl

theorem rejection : Comparators.GorbowAtomicSchemaCode.Rejection := by
  intro m raw ns
  have hraw : compileRaw m raw ns=none ↔ GorbowAtomicAnnotation.valid m raw ns=false := by
    constructor
    · intro h
      cases hg : GorbowAtomicAnnotation.valid m raw ns with
      | false => rfl
      | true =>
        obtain ⟨R,names,hr,hn,hi,hc,ha⟩ := (GorbowAtomicAnnotationProof.exactDomain m raw ns).mp hg
        have he := (exactRaw m raw ns _).mpr ⟨R,names,hr,hn,ha,hi,hc,rfl⟩
        rw [h] at he
        cases he
    · intro h; simp [compileRaw,h]
  refine ⟨hraw,?_⟩
  simpa only [compileNumber,Option.map_eq_none_iff] using hraw

theorem actualSemantics : Comparators.GorbowAtomicSchemaCode.ActualSemantics := by
  intro m raw ns out h
  obtain ⟨R,names,hr,hn,ha,hi,hc,ho⟩ := (exactNumeric m raw ns out).mp h
  exact ⟨atomicAxiom R names,ho,GorbowAtomicTruthProof.atomicSchemas _ _ R names ha hi hc⟩

private theorem pr_sub : Primrec (fun p : Nat × List Nat × List Nat =>
    GorbowSubstitutionCode.substituteFormulaCode p.1 p.2.2.length (valueSlots p.1 p.2.2) p.2.1) := by
  have hn : Primrec (fun p : Nat × List Nat × List Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hr : Primrec (fun p : Nat × List Nat × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd := GorbowAtomicParameterCodeProof.uniformPrograms.2.2.2.1.comp (Primrec.fst.pair hn)
  exact GorbowSubstitutionCodeProof.uniformPrograms.2.2.2.2.comp
    (Primrec.fst.pair ((Primrec.list_length.comp hn).pair (hd.pair hr)))
private theorem pr_binary (tag : Nat) : Primrec (fun p : List Nat × List Nat => binary tag p.1 p.2) :=
  Primrec.list_cons.comp (Primrec.const tag) (Primrec.list_append.comp Primrec.fst Primrec.snd)
private theorem pr_assembly : Primrec (fun p : (Nat × List Nat × List Nat) × List Nat =>
    binary 8 (binary 7 (unary 5 (instanceRaw p.1.1 p.1.2.1 p.1.2.2)) p.2)
      (binary 7 p.2 (unary 5 (instanceRaw p.1.1 p.1.2.1 p.1.2.2)))) := by
  have hl : Primrec (fun p : (Nat × List Nat × List Nat) × List Nat =>
      unary 5 (instanceRaw p.1.1 p.1.2.1 p.1.2.2)) :=
    Primrec.list_cons.comp (Primrec.const 5)
      (GorbowAtomicParameterCodeProof.uniformPrograms.2.2.2.2.comp Primrec.fst)
  exact (pr_binary 8).comp (((pr_binary 7).comp (hl.pair Primrec.snd)).pair
    ((pr_binary 7).comp (Primrec.snd.pair hl)))
private theorem pr_body : Primrec (fun p : Nat × List Nat × List Nat => bodyRaw p.1 p.2.1 p.2.2) := by
  have h := Primrec.option_map pr_sub pr_assembly.to₂
  exact h.of_eq (fun p => by
    unfold bodyRaw
    cases GorbowSubstitutionCode.substituteFormulaCode p.1 p.2.2.length (valueSlots p.1 p.2.2) p.2.1 <;> rfl)
private theorem pr_raw : Primrec (fun p : Nat × List Nat × List Nat => compileRaw p.1 p.2.1 p.2.2) := by
  have hf : Primrec (fun p : (Nat × List Nat × List Nat) × List Nat =>
      GorbowRegistryTermCode.closeRaw p.1.2.2.length p.2) :=
    GorbowRegistryTermCodeProof.uniformPrograms.2.2.2.2.2.comp
      ((Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd)
  exact Primrec.ite (Primrec.eq.comp GorbowAtomicAnnotationProof.uniformPrograms.2.2.2 (Primrec.const true))
    (Primrec.option_map pr_body hf.to₂) (Primrec.const none)
private theorem pr_number : Primrec (fun p : Nat × List Nat × List Nat => compileNumber p.1 p.2.1 p.2.2) :=
  Primrec.option_map pr_raw (GorbowSortedSyntaxCodeProof.uniformPrograms.2.2.1.comp Primrec.snd).to₂

theorem uniformPrograms : Comparators.GorbowAtomicSchemaCode.UniformPrograms := ⟨pr_body,pr_raw,pr_number⟩
theorem gorbowAtomicSchemaCode : Comparators.GorbowAtomicSchemaCode.Target :=
  ⟨bodyCalibration,originalCalibration,exactRaw,exactNumeric,rejection,actualSemantics,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowAtomicSchemaCodeProof
