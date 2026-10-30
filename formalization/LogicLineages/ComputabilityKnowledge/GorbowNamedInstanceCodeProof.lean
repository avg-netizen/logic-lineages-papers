module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowNamedInstanceCode
public import LogicLineages.ComputabilityKnowledge.GorbowNamedNumericCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaCompositionProof
public import LogicLineages.ComputabilityKnowledge.GorbowInstanceCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowClosedTermCodeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedInstanceCodeProof
open GorbowSyntax GorbowFreeSupport GorbowNamedBinding GorbowFormulaComposition GorbowCodeConstructors
open GorbowRawContextBound GorbowNamedBindingCode GorbowNamedNumericCode GorbowNamedInstanceCode

private theorem selectedRaw (n : Nat) (φ : Formula n) (v : Fin n) (hs : formulaSupport φ={v.val}) :
    selectCode (rawBound (GorbowFormulaPrefixCode.encode φ)) v.val (GorbowFormulaPrefixCode.encode φ)=
      some (GorbowFormulaPrefixCode.encode (selectVariable v φ)) := by
  obtain ⟨hin,ha,hx,hsel⟩ := GorbowNamedNumericCodeProof.originalCalibration n φ v hs
  rw [selectNumber,hin] at hsel
  simp only [bind,Option.bind_some] at hsel
  cases ho : selectCode (rawBound (GorbowFormulaPrefixCode.encode φ)) v.val (GorbowFormulaPrefixCode.encode φ) with
  | none => simp [ho] at hsel
  | some out =>
    have he : number out=formulaNumber (selectVariable v φ) := by simpa [ho] using hsel
    have hr : out=GorbowFormulaPrefixCode.encode (selectVariable v φ) := Encodable.encode_injective he
    exact congrArg some hr

private theorem decodeTerm (t : Term 0) : GorbowNumericCertificate.decodeFormula (termNumber t)=some (GorbowTermPrefixCode.encode t) :=
  (GorbowNumericCertificateProof.exactDecoding.1 _ _).mpr rfl

theorem originalCalibration : Comparators.GorbowNamedInstanceCode.OriginalCalibration := by
  intro n φ v hs t
  have hi := (GorbowNamedNumericCodeProof.originalCalibration n φ v hs).1
  have hsel := selectedRaw n φ v hs
  have hout := (GorbowInstanceCodeProof.exactInstance 0 _ _ _).mpr ⟨selectVariable v φ,t,rfl,rfl,rfl⟩
  simp only [instanceNumber,hi,bind,Option.bind_some,hsel,decodeTerm,hout,pure,Option.pure_def]
  rw [GorbowFormulaCompositionProof.namedSyntax]
  rfl

private theorem bindSome {α β : Type} (o : Option α) (f : α → Option β) (b : β) :
    (o >>= f)=some b ↔ ∃ a,o=some a ∧ f a=some b := by cases o <;> simp

theorem exactOutput : Comparators.GorbowNamedInstanceCode.ExactOutput := by
  intro v formulaCode termCode out
  constructor
  · intro h
    obtain ⟨raw,hin,h⟩ := (bindSome _ _ out).mp h
    obtain ⟨selected,hsel,h⟩ := (bindSome _ _ out).mp h
    obtain ⟨traw,ht,h⟩ := (bindSome _ _ out).mp h
    obtain ⟨outraw,ho,hn⟩ := (bindSome _ _ out).mp h
    obtain ⟨n,φ,hv,hcode,hs,hr⟩ := (GorbowNamedNumericCodeProof.exactInput v formulaCode raw).mp hin
    obtain ⟨A,t,hA,he,heout⟩ := (GorbowInstanceCodeProof.exactInstance 0 selected traw outraw).mp ho
    have hterm : termCode=termNumber t := by
      have hh := (GorbowNumericCertificateProof.exactDecoding.1 termCode traw).mp ht
      simpa [termNumber,number,he] using hh.symm
    have hc := originalCalibration n φ ⟨v,hv⟩ hs t
    have hn' : number outraw=out := by simpa using hn
    have horiginal : instanceNumber v formulaCode termCode=some out := by
      simp [instanceNumber,hin,hsel,ht,ho,hn']
    rw [hcode,hterm,hc] at horiginal
    exact ⟨n,φ,hv,t,hcode,hs,hterm,(Option.some.inj horiginal).symm⟩
  · rintro ⟨n,φ,hv,t,rfl,hs,rfl,rfl⟩
    exact originalCalibration n φ ⟨v,hv⟩ hs t

theorem outputDomain : Comparators.GorbowNamedInstanceCode.OutputDomain := by
  intro v formulaCode termCode out h
  obtain ⟨n,φ,hv,t,hc,hs,ht,ho⟩ := (exactOutput v formulaCode termCode out).mp h
  exact ⟨namedClosedInstance ⟨v,hv⟩ φ t,ho⟩

theorem originalSemantics : Comparators.GorbowNamedInstanceCode.OriginalSemantics := by
  intro n φ v hs t
  exact ⟨namedClosedInstance v φ t,originalCalibration n φ v hs t,
    GorbowFormulaCompositionProof.namedSemantics n v φ hs t⟩

theorem exactRejection : Comparators.GorbowNamedInstanceCode.ExactRejection := by
  intro v formulaCode termCode
  constructor
  · intro h
    by_cases hn : namedInput v formulaCode=none
    · exact Or.inl hn
    · right
      cases hi : namedInput v formulaCode with
      | none => exact (hn hi).elim
      | some raw =>
        obtain ⟨n,φ,hv,hc,hs,hr⟩ := (GorbowNamedNumericCodeProof.exactInput v formulaCode raw).mp hi
        cases ht : GorbowClosedTermCode.fullTermCode termCode with
        | false => rfl
        | true =>
          obtain ⟨t,he⟩ := (GorbowClosedTermCodeProof.exactNumericDomains.1 termCode).mp ht
          rw [hc,he,originalCalibration n φ ⟨v,hv⟩ hs t] at h
          contradiction
  · intro h
    cases hi : instanceNumber v formulaCode termCode with
    | none => rfl
    | some out =>
      obtain ⟨n,φ,hv,t,hc,hs,ht,ho⟩ := (exactOutput v formulaCode termCode out).mp hi
      rcases h with h | h
      · have hh := (GorbowNamedNumericCodeProof.originalCalibration n φ ⟨v,hv⟩ hs).1
        rw [hc,hh] at h
        contradiction
      · have hh := (GorbowClosedTermCodeProof.exactNumericDomains.1 termCode).mpr ⟨t,ht⟩
        rw [hh] at h
        contradiction

private theorem pr_instanceRaw : Primrec (fun p : (Nat × Nat × Nat) × List Nat => do
    let traw ← GorbowNumericCertificate.decodeFormula p.1.2.2
    let out ← GorbowInstanceCode.instanceCode 0 p.2 traw
    pure (number out)) := by
  have hd : Primrec (fun p : (Nat × Nat × Nat) × List Nat => GorbowNumericCertificate.decodeFormula p.1.2.2) := GorbowNumericCertificateProof.uniformPrograms.1.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hi : Primrec (fun p : ((Nat × Nat × Nat) × List Nat) × List Nat => GorbowInstanceCode.instanceCode 0 p.1.2 p.2) := GorbowInstanceCodeProof.uniformPrograms.2.1.comp
    ((Primrec.const 0).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
  have hm := Primrec.option_map hi (GorbowCodeConstructorsProof.uniformPrograms.2.2.2.2.comp Primrec.snd).to₂
  have h := Primrec.option_bind hd hm.to₂
  apply h.of_eq
  intro p
  cases ht : GorbowNumericCertificate.decodeFormula p.1.2.2 with
  | none => simp [ht]
  | some traw => cases ho : GorbowInstanceCode.instanceCode 0 p.2 traw <;> simp [ht,ho]

private theorem pr_selected : Primrec (fun p : (Nat × Nat × Nat) × List Nat => do
    let selected ← selectCode (rawBound p.2) p.1.1 p.2
    let traw ← GorbowNumericCertificate.decodeFormula p.1.2.2
    let out ← GorbowInstanceCode.instanceCode 0 selected traw
    pure (number out)) := by
  have hb := GorbowRawContextBoundProof.uniformPrograms.1.comp (Primrec.snd : Primrec (fun p : (Nat × Nat × Nat) × List Nat => p.2))
  have hv := Primrec.fst.comp (Primrec.fst : Primrec (fun p : (Nat × Nat × Nat) × List Nat => p.1))
  have hs := GorbowNamedBindingCodeProof.uniformPrograms.2.2.2.2.comp (hb.pair (hv.pair Primrec.snd))
  exact Primrec.option_bind hs (pr_instanceRaw.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

theorem uniformProgram : Comparators.GorbowNamedInstanceCode.UniformProgram := by
  have hv : Primrec (fun p : Nat × Nat × Nat => p.1) := Primrec.fst
  have hf : Primrec (fun p : Nat × Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  exact Primrec.option_bind (GorbowNamedNumericCodeProof.uniformPrograms.1.comp (hv.pair hf)) pr_selected.to₂

theorem gorbowNamedInstanceCode : Comparators.GorbowNamedInstanceCode.Target :=
  ⟨originalCalibration,exactOutput,outputDomain,originalSemantics,exactRejection,uniformProgram⟩
end LogicLineages.ComputabilityKnowledge.GorbowNamedInstanceCodeProof
