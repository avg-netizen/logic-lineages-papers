module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowInstanceCode
public import LogicLineages.ComputabilityKnowledge.GorbowSubstitutionCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructorsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowInstanceCodeProof
open GorbowSyntax GorbowInstanceCode GorbowLiftedDictionary GorbowCodeConstructors

private theorem variableDictionaryExact (n b : Nat) :
    variableDictionary n b = dictionary (fun i : Fin n => Term.var (GorbowTermShiftCode.shiftVar n b i)) := by
  apply List.ext_getElem
  · simp [variableDictionary,dictionary]
  · intro i hi hj
    simp [variableDictionary,dictionary,GorbowTermPrefixCode.encode,variableCode,GorbowTermShiftCode.shiftVar]

private theorem dictionaryCases {n m : Nat} (t : Term m) (σ : Fin n → Term m) :
    dictionary (Fin.cases t σ) = GorbowTermPrefixCode.encode t :: dictionary σ := by
  simp [dictionary,List.ofFn_succ]

private theorem instanceEncoded (n : Nat) (φ : Formula (n+1)) (t : Term n) :
    instanceCode n (GorbowFormulaPrefixCode.encode φ) (GorbowTermPrefixCode.encode t) =
      some (GorbowFormulaPrefixCode.encode (GorbowStandardInstances.instantiate φ t)) := by
  apply (GorbowSubstitutionCodeProof.exactOutput.2 (n+1) n _ _ _).mpr
  refine ⟨Fin.cases t Term.var,φ,?_,rfl,rfl⟩
  rw [dictionaryCases,variableDictionaryExact]
  rfl

private theorem weakeningEncoded (n : Nat) (φ : Formula n) :
    weakeningCode n (GorbowFormulaPrefixCode.encode φ) =
      some (GorbowFormulaPrefixCode.encode (GorbowPACore.weaken φ)) := by
  apply (GorbowSubstitutionCodeProof.exactOutput.2 n (n+1) _ _ _).mpr
  exact ⟨fun i => .var i.succ,φ,variableDictionaryExact n 1,rfl,rfl⟩

private theorem successorEncoded (n : Nat) (φ : Formula (n+1)) :
    successorCode n (GorbowFormulaPrefixCode.encode φ) =
      some (GorbowFormulaPrefixCode.encode (GorbowStandardInduction.successorInstance φ)) := by
  apply (GorbowSubstitutionCodeProof.exactOutput.2 (n+1) (n+1) _ _ _).mpr
  refine ⟨Fin.cases (.succ (.var 0)) (fun i : Fin n => .var i.succ),φ,?_,rfl,rfl⟩
  rw [dictionaryCases,variableDictionaryExact]
  rfl

private theorem inductionEncoded (n : Nat) (φ : Formula (n+1)) :
    inductionCode n (GorbowFormulaPrefixCode.encode φ) =
      some (GorbowFormulaPrefixCode.encode (GorbowStandardInduction.inductionAxiom φ)) := by
  have hb := instanceEncoded n φ .zero
  have hs := successorEncoded n φ
  simp only [GorbowTermPrefixCode.encode] at hb
  simp only [inductionCode,hb,hs,bind,Option.bind_some,
    GorbowStandardInduction.inductionAxiom,GorbowFormulaPrefixCode.encode,binary,unary]

theorem exactInstance : Comparators.GorbowInstanceCode.ExactInstance := by
  intro n raw traw out
  constructor
  · intro h
    obtain ⟨σ,φ,hd,hr,ho⟩ := (GorbowSubstitutionCodeProof.exactOutput.2 (n+1) n _ raw out).mp h
    have ht : traw = GorbowTermPrefixCode.encode (σ 0) := by
      have he := congrArg (fun d : List (List Nat) => d.getD 0 []) hd
      have hc : (dictionary σ).getD 0 [] = GorbowTermPrefixCode.encode (σ 0) :=
        (GorbowLiftedDictionaryProof.dictionaryCalibration (n+1) n σ).2.2 0
      exact (show traw = (dictionary σ).getD 0 [] from by simpa only [List.getD_cons_zero] using he).trans hc
    subst raw
    subst traw
    rw [instanceEncoded] at h
    exact ⟨φ,σ 0,rfl,rfl,(Option.some.inj h).symm⟩
  · rintro ⟨φ,t,rfl,rfl,rfl⟩
    exact instanceEncoded n φ t

theorem exactWeakening : Comparators.GorbowInstanceCode.ExactWeakening := by
  intro n raw out
  constructor
  · intro h
    obtain ⟨σ,φ,hd,hr,ho⟩ := (GorbowSubstitutionCodeProof.exactOutput.2 n (n+1) _ raw out).mp h
    subst raw
    rw [weakeningEncoded] at h
    exact ⟨φ,rfl,(Option.some.inj h).symm⟩
  · rintro ⟨φ,rfl,rfl⟩
    exact weakeningEncoded n φ

theorem exactSuccessor : Comparators.GorbowInstanceCode.ExactSuccessor := by
  intro n raw out
  constructor
  · intro h
    obtain ⟨σ,φ,hd,hr,ho⟩ := (GorbowSubstitutionCodeProof.exactOutput.2 (n+1) (n+1) _ raw out).mp h
    subst raw
    rw [successorEncoded] at h
    exact ⟨φ,rfl,(Option.some.inj h).symm⟩
  · rintro ⟨φ,rfl,rfl⟩
    exact successorEncoded n φ

theorem exactInduction : Comparators.GorbowInstanceCode.ExactInduction := by
  intro n raw out
  constructor
  · intro h
    cases hb : instanceCode n raw [1] with
    | none => simp [inductionCode,hb] at h
    | some base =>
        obtain ⟨φ,t,hr,ht,ho⟩ := (exactInstance n raw [1] base).mp hb
        subst raw
        rw [inductionEncoded] at h
        exact ⟨φ,rfl,(Option.some.inj h).symm⟩
  · rintro ⟨φ,rfl,rfl⟩
    exact inductionEncoded n φ

private theorem rejection {α : Type} (f : List Nat → Option (List Nat))
    (decode : List Nat → Option α) (encode output : α → List Nat)
    (hf : ∀ raw out, f raw = some out ↔ ∃ a, raw = encode a ∧ out = output a)
    (hd : ∀ raw a, decode raw = some a ↔ raw = encode a) :
    ∀ raw, f raw = none ↔ decode raw = none := by
  intro raw
  constructor
  · intro h
    cases ha : decode raw with
    | none => rfl
    | some a =>
        have hc := (hf raw (output a)).mpr ⟨a,(hd raw a).mp ha,rfl⟩
        rw [h] at hc
        cases hc
  · intro h
    cases ho : f raw with
    | none => rfl
    | some out =>
        obtain ⟨a,ha,_⟩ := (hf raw out).mp ho
        have hc := (hd raw a).mpr ha
        rw [h] at hc
        cases hc

theorem exactRejection : Comparators.GorbowInstanceCode.ExactRejection := by
  refine ⟨?_,?_,?_,?_⟩
  · intro n raw traw
    constructor
    · intro h
      cases hd : GorbowFormulaPrefixCode.decode (n+1) raw with
      | none => exact Or.inl rfl
      | some φ =>
          cases ht : GorbowTermPrefixCode.decode n traw with
          | none => exact Or.inr rfl
          | some t =>
              have hc := (exactInstance n raw traw _).mpr
                ⟨φ,t,(GorbowFormulaPrefixCodeProof.decoderExact (n+1) raw φ).mp hd,
                  (GorbowTermPrefixCodeProof.decoderExact n traw t).mp ht,rfl⟩
              rw [h] at hc
              cases hc
    · intro h
      cases ho : instanceCode n raw traw with
      | none => rfl
      | some out =>
          obtain ⟨φ,t,hr,ht,_⟩ := (exactInstance n raw traw out).mp ho
          have hf := (GorbowFormulaPrefixCodeProof.decoderExact (n+1) raw φ).mpr hr
          have hu := (GorbowTermPrefixCodeProof.decoderExact n traw t).mpr ht
          rcases h with h | h
          · rw [h] at hf; cases hf
          · rw [h] at hu; cases hu
  · intro n
    exact rejection (weakeningCode n) (GorbowFormulaPrefixCode.decode n) GorbowFormulaPrefixCode.encode
      (fun φ => GorbowFormulaPrefixCode.encode (GorbowPACore.weaken φ)) (exactWeakening n)
      (GorbowFormulaPrefixCodeProof.decoderExact n)
  · intro n
    exact rejection (successorCode n) (GorbowFormulaPrefixCode.decode (n+1)) GorbowFormulaPrefixCode.encode
      (fun φ => GorbowFormulaPrefixCode.encode (GorbowStandardInduction.successorInstance φ)) (exactSuccessor n)
      (GorbowFormulaPrefixCodeProof.decoderExact (n+1))
  · intro n
    exact rejection (inductionCode n) (GorbowFormulaPrefixCode.decode (n+1)) GorbowFormulaPrefixCode.encode
      (fun φ => GorbowFormulaPrefixCode.encode (GorbowStandardInduction.inductionAxiom φ)) (exactInduction n)
      (GorbowFormulaPrefixCodeProof.decoderExact (n+1))
private theorem pr_variableDictionary : Primrec (fun p : Nat × Nat => variableDictionary p.1 p.2) :=
  Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (GorbowCodeConstructorsProof.uniformPrograms.1.comp
      (Primrec.nat_add.comp Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂

private theorem pr_instance : Primrec (fun p : Nat × List Nat × List Nat => instanceCode p.1 p.2.1 p.2.2) := by
  have hn : Primrec (fun p : Nat × List Nat × List Nat => p.1) := Primrec.fst
  have hr : Primrec (fun p : Nat × List Nat × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : Nat × List Nat × List Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hd := Primrec.list_cons.comp ht (pr_variableDictionary.comp (hn.pair (Primrec.const 0)))
  exact GorbowSubstitutionCodeProof.uniformPrograms.2.2.2.2.comp
    ((Primrec.succ.comp hn).pair (hn.pair (hd.pair hr)))

private theorem pr_weakening : Primrec (fun p : Nat × List Nat => weakeningCode p.1 p.2) :=
  GorbowSubstitutionCodeProof.uniformPrograms.2.2.2.2.comp
    (Primrec.fst.pair ((Primrec.succ.comp Primrec.fst).pair
      ((pr_variableDictionary.comp (Primrec.fst.pair (Primrec.const 1))).pair Primrec.snd)))

private theorem pr_successor : Primrec (fun p : Nat × List Nat => successorCode p.1 p.2) := by
  have hn : Primrec (fun p : Nat × List Nat => p.1+1) := Primrec.succ.comp Primrec.fst
  have hd : Primrec (fun p : Nat × List Nat => [2,0,0] :: variableDictionary p.1 1) :=
    Primrec.list_cons.comp (Primrec.const [2,0,0])
      (pr_variableDictionary.comp (Primrec.fst.pair (Primrec.const 1)))
  exact GorbowSubstitutionCodeProof.uniformPrograms.2.2.2.2.comp (hn.pair (hn.pair (hd.pair Primrec.snd)))

private theorem pr_unary {α : Type} [Primcodable α] (tag : Nat) {f : α → List Nat} (hf : Primrec f) :
    Primrec (fun x => unary tag (f x)) :=
  GorbowCodeConstructorsProof.uniformPrograms.2.1.comp ((Primrec.const tag).pair hf)

private theorem pr_binary {α : Type} [Primcodable α] (tag : Nat) {f g : α → List Nat} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => binary tag (f x) (g x)) :=
  GorbowCodeConstructorsProof.uniformPrograms.2.2.1.comp ((Primrec.const tag).pair (hf.pair hg))

private theorem pr_inductionResult : Primrec (fun p : List Nat × List Nat × List Nat =>
    binary 7 p.2.1 (binary 7 (unary 10 (binary 7 p.1 p.2.2)) (unary 10 p.1))) :=
  pr_binary 7 (Primrec.fst.comp Primrec.snd)
    (pr_binary 7 (pr_unary 10 (pr_binary 7 Primrec.fst (Primrec.snd.comp Primrec.snd)))
      (pr_unary 10 Primrec.fst))

private theorem pr_inductionAssembly : Primrec (fun p : ((Nat × List Nat) × List Nat) × List Nat =>
    some (binary 7 p.1.2 (binary 7 (unary 10 (binary 7 p.1.1.2 p.2)) (unary 10 p.1.1.2)))) :=
  Primrec.option_some.comp (pr_inductionResult.comp
    ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)))

private theorem pr_induction : Primrec (fun p : Nat × List Nat => inductionCode p.1 p.2) := by
  have hb := pr_instance.comp (Primrec.fst.pair (Primrec.snd.pair (Primrec.const [1])))
  have hi := Primrec.option_bind (pr_successor.comp Primrec.fst) pr_inductionAssembly.to₂
  have h := Primrec.option_bind hb hi.to₂
  exact h.of_eq (fun _ => rfl)

theorem uniformPrograms : Comparators.GorbowInstanceCode.UniformPrograms :=
  ⟨pr_variableDictionary,pr_instance,pr_weakening,pr_successor,pr_induction⟩

theorem gorbowInstanceCode : Comparators.GorbowInstanceCode.Target :=
  ⟨exactInstance,exactWeakening,exactSuccessor,exactInduction,exactRejection,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowInstanceCodeProof
