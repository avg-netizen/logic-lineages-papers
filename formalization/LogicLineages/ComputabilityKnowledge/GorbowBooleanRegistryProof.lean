module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowBooleanRegistry
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryDecoderProof
public import LogicLineages.ComputabilityKnowledge.GorbowNumericCertificateProof
public import LogicLineages.ComputabilityKnowledge.GorbowSyntaxValidationProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowBooleanRegistryProof
open GorbowSyntax GorbowCodeConstructors GorbowRegistryTuple GorbowRegistryDecoder GorbowNumericCertificate GorbowBooleanRegistry

private theorem decodeNumber (raw : List Nat) : decodeFormula (number raw)=some raw :=
  (GorbowNumericCertificateProof.exactDecoding.1 _ _).mpr rfl
private theorem decodeHeaderAt (arity tag : Nat) (args : List Nat) :
    decodeHeader (header arity tag args)=some (arity,tag,args) :=
  (GorbowRegistryDecoderProof.headerExact _ _ _ _).mpr rfl

theorem numericConstructors : Comparators.GorbowBooleanRegistry.NumericConstructors := by
  constructor
  · intro tag raw; simp [unaryNumber,decodeNumber]
  · intro tag a b; simp [binaryNumber,decodeNumber]
private theorem unaryAt (tag : Nat) (raw : List Nat) : unaryNumber tag (number raw)=number (unary tag raw) := numericConstructors.1 tag raw
private theorem binaryAt (tag : Nat) (a b : List Nat) : binaryNumber tag (number a) (number b)=number (binary tag a b) := numericConstructors.2 tag a b

theorem exactSentencehood : Comparators.GorbowBooleanRegistry.ExactSentencehood := by
  intro code
  constructor
  · intro h
    cases hd : decodeFormula code with
    | none => simp [sentenceCode,hd] at h
    | some raw =>
      have hv : GorbowSyntaxValidation.validFormula 0 raw=true := by simpa [sentenceCode,hd] using h
      obtain ⟨σ,hs⟩ := (GorbowSyntaxValidationProof.exactTypedDomain.2 0 raw).mp hv
      have he := (GorbowFormulaPrefixCodeProof.decoderExact 0 raw σ).mp hs
      have hc := (GorbowNumericCertificateProof.exactDecoding.1 code raw).mp hd
      exact ⟨σ,by simpa [formulaNumber,number,he] using hc.symm⟩
  · rintro ⟨σ,rfl⟩
    have hv := (GorbowSyntaxValidationProof.exactTypedDomain.2 0 (GorbowFormulaPrefixCode.encode σ)).mpr
      ⟨σ,(GorbowFormulaPrefixCodeProof.decoderExact 0 _ σ).mpr rfl⟩
    simpa [sentenceCode,formulaNumber,decodeNumber] using hv

private theorem sentenceAt (σ : Sentence) : sentenceCode (formulaNumber σ)=true :=
  (exactSentencehood _).mpr ⟨σ,rfl⟩

theorem exactRelation : Comparators.GorbowBooleanRegistry.ExactRelation := by
  intro code
  constructor
  · intro h
    cases hd : decodeHeader code with
    | none => simp [relationProgram,hd] at h
    | some p =>
      obtain ⟨arity,tag,args⟩ := p
      have hp : (arity=1 ∧ tag=0 ∧ args.length=1) ∧ sentenceCode (args.getD 0 0)=true := by
        simpa [relationProgram,hd] using h
      obtain ⟨rfl,rfl,hlen⟩ := hp.1
      obtain ⟨c,rfl⟩ := List.length_eq_one_iff.mp hlen
      obtain ⟨σ,hσ⟩ := (exactSentencehood c).mp (by simpa using hp.2)
      have he := (GorbowRegistryDecoderProof.headerExact _ _ _ _).mp hd
      exact ⟨σ,by simpa [hσ] using he.symm⟩
  · rintro ⟨σ,rfl⟩
    simp [relationProgram,decodeHeaderAt,sentenceAt]

theorem functionCalibration : Comparators.GorbowBooleanRegistry.FunctionCalibration := by
  intro σ τ
  simp [functionProgram,decodeHeaderAt,formulaNumber,unaryAt,binaryAt,GorbowFormulaPrefixCode.encode,unary,binary]

theorem malformedDefaults : Comparators.GorbowBooleanRegistry.MalformedDefaults := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro code h; simp [relationProgram,functionProgram,h]
  · intro arity tag args h; simp [relationProgram,decodeHeaderAt,h]
  · intro arity tag args h1 h2; simp [functionProgram,decodeHeaderAt,h1,h2]
  · intro tag code h; simp [unaryNumber,h]
  · intro tag a b h
    rcases h with h | h
    · simp [binaryNumber,h]
    · simp [binaryNumber,h]

private theorem pr_decodeFormula : Primrec decodeFormula := GorbowNumericCertificateProof.uniformPrograms.1
private theorem pr_decodeHeader : Primrec decodeHeader := GorbowRegistryDecoderProof.uniformPrograms.2.2.2.2
private theorem pr_number : Primrec number := GorbowCodeConstructorsProof.uniformPrograms.2.2.2.2
private theorem pr_unaryNumber : Primrec (fun p : Nat × Nat => unaryNumber p.1 p.2) := by
  have hl : Primrec (fun p : (Nat × Nat) × List Nat => number (unary p.1.1 p.2)) :=
    pr_number.comp (GorbowCodeConstructorsProof.uniformPrograms.2.1.comp
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))
  exact Primrec.option_getD.comp (Primrec.option_map (pr_decodeFormula.comp Primrec.snd) hl.to₂) (Primrec.const 0)
private theorem pr_binaryInner : Primrec (fun p : (Nat × Nat × Nat) × List Nat =>
    (decodeFormula p.1.2.2).map (fun rb => number (binary p.1.1 p.2 rb))) := by
  have hl : Primrec (fun p : ((Nat × Nat × Nat) × List Nat) × List Nat =>
      number (binary p.1.1.1 p.1.2 p.2)) :=
    pr_number.comp (GorbowCodeConstructorsProof.uniformPrograms.2.2.1.comp
      ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)))
  exact Primrec.option_map (pr_decodeFormula.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) hl.to₂
private theorem pr_binaryOption : Primrec (fun p : Nat × Nat × Nat => do
    let ra ← decodeFormula p.2.1
    let rb ← decodeFormula p.2.2
    pure (number (binary p.1 ra rb))) := by
  have h := Primrec.option_bind (pr_decodeFormula.comp (Primrec.fst.comp Primrec.snd)) pr_binaryInner.to₂
  exact h.of_eq (fun p => by
    cases ha : decodeFormula p.2.1 <;> cases hb : decodeFormula p.2.2 <;> simp [ha,hb])
private theorem pr_binaryNumber : Primrec (fun p : Nat × Nat × Nat => binaryNumber p.1 p.2.1 p.2.2) :=
  Primrec.option_getD.comp pr_binaryOption (Primrec.const 0)
private theorem pr_sentenceCode : Primrec sentenceCode := by
  have hl : Primrec (fun p : Nat × List Nat => GorbowSyntaxValidation.validFormula 0 p.2) :=
    GorbowSyntaxValidationProof.uniformPrograms.2.2.2.2.comp ((Primrec.const 0).pair Primrec.snd)
  have h := Primrec.option_casesOn pr_decodeFormula (Primrec.const false) hl.to₂
  exact h.of_eq (fun c => by cases hd : decodeFormula c <;> simp [sentenceCode,hd])
private abbrev Header := Nat × Nat × List Nat
private theorem pr_tag : Primrec (fun p : Header => p.2.1) := Primrec.fst.comp Primrec.snd
private theorem pr_args : Primrec (fun p : Header => p.2.2) := Primrec.snd.comp Primrec.snd
private theorem pr_arg (i : Nat) : Primrec (fun p : Header => p.2.2.getD i 0) :=
  (Primrec.list_getD 0).comp pr_args (Primrec.const i)
private theorem pr_unaryGuard : PrimrecPred (fun p : Header => p.1=1 ∧ p.2.1=0 ∧ p.2.2.length=1) :=
  (Primrec.eq.comp Primrec.fst (Primrec.const 1)).and
    ((Primrec.eq.comp pr_tag (Primrec.const 0)).and (Primrec.eq.comp (Primrec.list_length.comp pr_args) (Primrec.const 1)))
private theorem pr_binaryGuard : PrimrecPred (fun p : Header => p.1=2 ∧ p.2.1<3 ∧ p.2.2.length=2) :=
  (Primrec.eq.comp Primrec.fst (Primrec.const 2)).and
    ((Primrec.nat_lt.comp pr_tag (Primrec.const 3)).and (Primrec.eq.comp (Primrec.list_length.comp pr_args) (Primrec.const 2)))
private theorem pr_relationBody : Primrec (fun p : Header =>
    decide (p.1=1 ∧ p.2.1=0 ∧ p.2.2.length=1) && sentenceCode (p.2.2.getD 0 0)) :=
  Primrec.and.comp pr_unaryGuard.decide (pr_sentenceCode.comp (pr_arg 0))
private theorem pr_relationProgram : Primrec relationProgram := by
  have h := Primrec.option_casesOn pr_decodeHeader (Primrec.const false) (pr_relationBody.comp Primrec.snd).to₂
  exact h.of_eq (fun code => by cases hd : decodeHeader code <;> simp [relationProgram,hd])
private theorem pr_functionBody : Primrec (fun p : Header =>
    if p.1=1 ∧ p.2.1=0 ∧ p.2.2.length=1 then unaryNumber 6 (p.2.2.getD 0 0)
    else if p.1=2 ∧ p.2.1<3 ∧ p.2.2.length=2 then binaryNumber (p.2.1+7) (p.2.2.getD 0 0) (p.2.2.getD 1 0)
    else 0) :=
  Primrec.ite pr_unaryGuard (pr_unaryNumber.comp ((Primrec.const 6).pair (pr_arg 0)))
    (Primrec.ite pr_binaryGuard (pr_binaryNumber.comp
      ((Primrec.nat_add.comp pr_tag (Primrec.const 7)).pair ((pr_arg 0).pair (pr_arg 1)))) (Primrec.const 0))
private theorem pr_functionProgram : Primrec functionProgram := by
  have h := Primrec.option_casesOn pr_decodeHeader (Primrec.const 0) (pr_functionBody.comp Primrec.snd).to₂
  exact h.of_eq (fun code => by cases hd : decodeHeader code <;> simp [functionProgram,hd])

theorem uniformPrograms : Comparators.GorbowBooleanRegistry.UniformPrograms :=
  ⟨pr_unaryNumber,pr_binaryNumber,pr_sentenceCode,pr_relationProgram,pr_functionProgram⟩

theorem gorbowBooleanRegistry : Comparators.GorbowBooleanRegistry.Target :=
  ⟨numericConstructors,exactSentencehood,exactRelation,functionCalibration,malformedDefaults,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowBooleanRegistryProof
