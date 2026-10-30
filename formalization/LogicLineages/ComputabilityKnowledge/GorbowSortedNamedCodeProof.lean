module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedNamedCode
public import LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedNumericCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedInstanceCodeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSortedNamedCodeProof
open GorbowSyntax GorbowSortedSyntaxCode GorbowSortedNamedCode GorbowFreeSupport GorbowNamedBinding GorbowFormulaComposition

private theorem evenMod (n : Nat) : tagFormula n%2=0 := by unfold tagFormula; omega
private theorem evenDiv (n : Nat) : tagFormula n/2=n := by unfold tagFormula; omega
private theorem oddMod (n : Nat) : tagTerm n%2=1 := by unfold tagTerm; omega
private theorem oddDiv (n : Nat) : tagTerm n/2=n := by unfold tagTerm; omega
private theorem variableAt (i : Nat) : decodeVariable (variableNumber i)=some i :=
  (GorbowSortedSyntaxCodeProof.actualCalibration.2.2.2.1 _ _).mpr rfl
private theorem inputsAt (i code : Nat) : decodeInputs (variableNumber i) (tagFormula code)=some (i,code) := by
  simp [decodeInputs,variableAt,evenMod,evenDiv]
private theorem inputsExact (varCode formula i code : Nat) :
    decodeInputs varCode formula=some (i,code) ↔ varCode=variableNumber i ∧ formula=tagFormula code := by
  constructor
  · intro h
    cases hd : decodeVariable varCode with
    | none => simp [decodeInputs,hd] at h
    | some j =>
      simp only [decodeInputs,hd,bind,Option.bind_some] at h
      split at h
      · rename_i hp
        have he := Option.some.inj h
        have hj : j=i := congrArg Prod.fst he
        have hc : formula/2=code := congrArg Prod.snd he
        subst j
        refine ⟨(GorbowSortedSyntaxCodeProof.actualCalibration.2.2.2.1 _ _).mp hd,?_⟩
        unfold tagFormula
        omega
      · simp at h
  · rintro ⟨rfl,rfl⟩
    exact inputsAt i code

theorem inputCalibration : Comparators.GorbowSortedNamedCode.InputCalibration :=
  fun n φ v => inputsAt v.val (GorbowCodeConstructors.formulaNumber φ)

theorem exactNamedDomain : Comparators.GorbowSortedNamedCode.ExactNamedDomain := by
  intro varCode formula
  constructor
  · intro h
    cases hd : decodeInputs varCode formula with
    | none => simp [namedFormula,hd] at h
    | some p =>
      rcases p with ⟨i,code⟩
      cases hi : GorbowNamedNumericCode.namedInput i code with
      | none => simp [namedFormula,hd,hi] at h
      | some raw =>
        obtain ⟨n,φ,hv,hcode,hs,hr⟩ := (GorbowNamedNumericCodeProof.exactInput i code raw).mp hi
        obtain ⟨hvcode,hfcode⟩ := (inputsExact varCode formula i code).mp hd
        exact ⟨n,φ,⟨i,hv⟩,hvcode,by simpa [formulaCode,hcode] using hfcode,hs⟩
  · rintro ⟨n,φ,v,rfl,rfl,hs⟩
    have hd := inputCalibration n φ v
    have hi := (GorbowNamedNumericCodeProof.originalCalibration n φ v hs).1
    simp [namedFormula,hd,hi]

theorem originalCalibration : Comparators.GorbowSortedNamedCode.OriginalCalibration := by
  intro n φ v hs
  have hd := inputCalibration n φ v
  obtain ⟨hin,ha,hx,hsel⟩ := GorbowNamedNumericCodeProof.originalCalibration n φ v hs
  refine ⟨?_,?_,?_⟩
  · simp [allNumber,formulaCode,inputsAt,ha]
  · simp [exNumber,formulaCode,inputsAt,hx]
  · intro t
    have ht := GorbowNamedInstanceCodeProof.originalCalibration n φ v hs t
    simp [instanceNumber,termCode,oddMod,oddDiv,formulaCode,inputsAt,ht]

private theorem someIff {α β : Type} (o : Option α) (p : Option β) (h : o=none ↔ p=none) :
    o.isSome=true ↔ p.isSome=true := by cases o <;> cases p <;> simp_all
private theorem instanceSome (i code term : Nat) :
    (GorbowNamedInstanceCode.instanceNumber i code term).isSome=true ↔
      (GorbowNamedNumericCode.namedInput i code).isSome=true ∧ GorbowClosedTermCode.fullTermCode term=true := by
  have h := GorbowNamedInstanceCodeProof.exactRejection i code term
  cases ho : GorbowNamedInstanceCode.instanceNumber i code term <;>
    cases hi : GorbowNamedNumericCode.namedInput i code <;>
    cases ht : GorbowClosedTermCode.fullTermCode term <;> simp_all

theorem exactDefinedness : Comparators.GorbowSortedNamedCode.ExactDefinedness := by
  intro varCode formula
  cases hd : decodeInputs varCode formula with
  | none => simp [allNumber,exNumber,instanceNumber,namedFormula,hd]
  | some p =>
    rcases p with ⟨i,code⟩
    obtain ⟨ha,hx,hsel⟩ := GorbowNamedNumericCodeProof.exactRejection i code
    have hea := someIff _ _ ha
    have hex := someIff _ _ hx
    refine ⟨by simpa [allNumber,namedFormula,hd] using hea,by simpa [exNumber,namedFormula,hd] using hex,?_⟩
    intro term
    by_cases hp : term%2=1
    · simpa [instanceNumber,namedFormula,hd,hp,GorbowSortedBooleanCode.fullTermCode] using instanceSome i code (term/2)
    · simp [instanceNumber,namedFormula,hd,hp,GorbowSortedBooleanCode.fullTermCode]

private theorem bindSome {α β : Type} (o : Option α) (f : α → Option β) (b : β) :
    (o >>= f)=some b ↔ ∃ a,o=some a ∧ f a=some b := by cases o <;> simp
private theorem mapSome {α β : Type} (f : α → β) (o : Option α) (b : β) :
    o.map f=some b ↔ ∃ a,o=some a ∧ f a=b := by cases o <;> simp

theorem outputDomains : Comparators.GorbowSortedNamedCode.OutputDomains := by
  intro varCode formula out
  constructor
  · intro h
    obtain ⟨p,hp,hr⟩ := (bindSome _ _ out).mp h
    obtain ⟨old,ho,he⟩ := (mapSome tagFormula _ out).mp hr
    obtain ⟨σ,hσ⟩ := (GorbowNamedNumericCodeProof.outputDomains p.1 p.2 old).1 ho
    exact ⟨σ,by rw [← he,hσ]; rfl⟩
  constructor
  · intro h
    obtain ⟨p,hp,hr⟩ := (bindSome _ _ out).mp h
    obtain ⟨old,ho,he⟩ := (mapSome tagFormula _ out).mp hr
    obtain ⟨σ,hσ⟩ := (GorbowNamedNumericCodeProof.outputDomains p.1 p.2 old).2.1 ho
    exact ⟨σ,by rw [← he,hσ]; rfl⟩
  · intro term h
    obtain ⟨p,hp,hr⟩ := (bindSome _ _ out).mp h
    split at hr
    · obtain ⟨old,ho,he⟩ := (mapSome tagFormula _ out).mp hr
      obtain ⟨σ,hσ⟩ := GorbowNamedInstanceCodeProof.outputDomain p.1 p.2 (term/2) old ho
      exact ⟨σ,by rw [← he,hσ]; rfl⟩
    · simp at hr

theorem originalSemantics : Comparators.GorbowSortedNamedCode.OriginalSemantics := by
  intro n φ v hs
  obtain ⟨σ,τ,A,ha,hx,hsel,hsem⟩ := GorbowNamedNumericCodeProof.originalSemantics n φ v hs
  have hd := inputCalibration n φ v
  refine ⟨σ,τ,?_,?_,?_⟩
  · simp [allNumber,formulaCode,inputsAt,ha]
  · simp [exNumber,formulaCode,inputsAt,hx]
  · intro I ρ
    exact ⟨(hsem I ρ).1,(hsem I ρ).2.1⟩

private theorem pr_inputs : Primrec (fun p : Nat × Nat => decodeInputs p.1 p.2) := by
  have hf : Primrec (fun p : (Nat × Nat) × Nat => p.1.2) := Primrec.snd.comp Primrec.fst
  have hp := Primrec.eq.comp (Primrec.nat_mod.comp hf (Primrec.const 2)) (Primrec.const 0)
  have hd := Primrec.nat_div.comp hf (Primrec.const 2)
  have hb := Primrec.ite hp (Primrec.option_some.comp (Primrec.snd.pair hd)) (Primrec.const none)
  exact Primrec.option_bind (GorbowSortedSyntaxCodeProof.uniformPrograms.2.2.2.2.2.2.2.1.comp Primrec.fst) hb.to₂
private theorem pr_named : Primrec (fun p : Nat × Nat => namedFormula p.1 p.2) :=
  Primrec.option_isSome.comp (Primrec.option_bind pr_inputs
    (GorbowNamedNumericCodeProof.uniformPrograms.1.comp Primrec.snd).to₂)
private theorem pr_lift (f : Nat → Nat → Option Nat) (hf : Primrec (fun p : Nat × Nat => f p.1 p.2)) :
    Primrec (fun p : Nat × Nat => do
      let q ← decodeInputs p.1 p.2
      (f q.1 q.2).map tagFormula) :=
  Primrec.option_bind pr_inputs (Primrec.option_map (hf.comp Primrec.snd)
    (GorbowSortedSyntaxCodeProof.uniformPrograms.1.comp Primrec.snd).to₂).to₂
private theorem pr_instanceBody : Primrec (fun p : (Nat × Nat × Nat) × (Nat × Nat) =>
    if p.1.2.2%2=1 then (GorbowNamedInstanceCode.instanceNumber p.2.1 p.2.2 (p.1.2.2/2)).map tagFormula else none) := by
  have ht : Primrec (fun p : (Nat × Nat × Nat) × (Nat × Nat) => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hi : Primrec (fun p : (Nat × Nat × Nat) × (Nat × Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hf : Primrec (fun p : (Nat × Nat × Nat) × (Nat × Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hp := Primrec.eq.comp (Primrec.nat_mod.comp ht (Primrec.const 2)) (Primrec.const 1)
  have hc := GorbowNamedInstanceCodeProof.uniformProgram.comp (hi.pair (hf.pair (Primrec.nat_div.comp ht (Primrec.const 2))))
  exact Primrec.ite hp (Primrec.option_map hc (GorbowSortedSyntaxCodeProof.uniformPrograms.1.comp Primrec.snd).to₂) (Primrec.const none)
private theorem pr_instance : Primrec (fun p : Nat × Nat × Nat => instanceNumber p.1 p.2.1 p.2.2) :=
  Primrec.option_bind (pr_inputs.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))) pr_instanceBody.to₂

theorem uniformPrograms : Comparators.GorbowSortedNamedCode.UniformPrograms :=
  ⟨pr_inputs,pr_named,pr_lift GorbowNamedNumericCode.allNumber GorbowNamedNumericCodeProof.uniformPrograms.2.1,
    pr_lift GorbowNamedNumericCode.exNumber GorbowNamedNumericCodeProof.uniformPrograms.2.2.1,pr_instance⟩
theorem gorbowSortedNamedCode : Comparators.GorbowSortedNamedCode.Target :=
  ⟨inputCalibration,exactNamedDomain,originalCalibration,exactDefinedness,outputDomains,originalSemantics,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowSortedNamedCodeProof
