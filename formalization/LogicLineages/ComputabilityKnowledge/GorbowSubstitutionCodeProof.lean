module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowSubstitutionCode
public import LogicLineages.ComputabilityKnowledge.GorbowLiftedDictionaryProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSubstitutionCodeProof
open GorbowSyntax GorbowSyntaxValidation GorbowLiftedDictionary GorbowSubstitutionCode

private theorem termScan (n m b : Nat) (σ : Fin n → Term m) (t : Term (n+b)) :
    ∀ (tasks : List Task) (acc : List Nat),
    (GorbowTermPrefixCode.encode t).foldl (subStep n m (dictionary σ)) (some ((0,n+b)::tasks),acc) =
      (some tasks,acc ++ GorbowTermPrefixCode.encode (GorbowSubstitution.substitute (liftN σ b) t)) := by
  induction t with
  | var i =>
      intro tasks acc
      simp [GorbowTermPrefixCode.encode, subStep, emit, step, expand, i.isLt,
        GorbowSubstitution.substitute, GorbowLiftedDictionaryProof.liftedCodeCalibration n m b σ i]
  | zero =>
      intro tasks acc
      simp [GorbowTermPrefixCode.encode, subStep, emit, step, expand, GorbowSubstitution.substitute]
  | succ t ih | universalFunction t ih =>
      intro tasks acc
      simp [GorbowTermPrefixCode.encode, subStep, emit, step, expand, ih,
        GorbowSubstitution.substitute, List.append_assoc]
  | add t u ht hu | mul t u ht hu =>
      intro tasks acc
      simp [GorbowTermPrefixCode.encode, List.foldl_append, subStep, emit, step, expand, ht, hu,
        GorbowSubstitution.substitute, List.append_assoc]

private theorem formulaScan (n m b : Nat) (σ : Fin n → Term m) (φ : Formula (n+b))
    (tasks : List Task) (acc : List Nat) :
    (GorbowFormulaPrefixCode.encode φ).foldl (subStep n m (dictionary σ)) (some ((1,n+b)::tasks),acc) =
      (some tasks,acc ++ GorbowFormulaPrefixCode.encode (GorbowFormulaSubstitution.substituteFormula (liftN σ b) φ)) := by
  cases φ with
  | equal t u | knowledge t u =>
      simp [GorbowFormulaPrefixCode.encode, List.foldl_append, subStep, emit, step, expand,
        termScan, GorbowFormulaSubstitution.substituteFormula, List.append_assoc]
  | universalRelation t | agent t | knowledgeAll t | truth t =>
      simp [GorbowFormulaPrefixCode.encode, subStep, emit, step, expand,
        termScan, GorbowFormulaSubstitution.substituteFormula, List.append_assoc]
  | neg φ =>
      have ih := formulaScan n m b σ φ
      simp [GorbowFormulaPrefixCode.encode, subStep, emit, step, expand,
        ih, GorbowFormulaSubstitution.substituteFormula, List.append_assoc]
  | imp φ ψ | conj φ ψ | disj φ ψ =>
      have hφ := formulaScan n m b σ φ
      have hψ := formulaScan n m b σ ψ
      simp [GorbowFormulaPrefixCode.encode, List.foldl_append, subStep, emit, step, expand,
        hφ, hψ, GorbowFormulaSubstitution.substituteFormula, List.append_assoc]
  | all φ =>
      have ih := formulaScan n m (b+1) σ φ
      change (GorbowFormulaPrefixCode.encode φ).foldl (subStep n m (dictionary σ))
        (some ((1,n+b+1)::tasks),acc ++ [10]) = _
      apply (ih tasks (acc ++ [10])).trans
      exact congrArg (fun xs => (some tasks,xs)) (List.append_assoc acc [10] _)
  | ex φ =>
      have ih := formulaScan n m (b+1) σ φ
      change (GorbowFormulaPrefixCode.encode φ).foldl (subStep n m (dictionary σ))
        (some ((1,n+b+1)::tasks),acc ++ [11]) = _
      apply (ih tasks (acc ++ [11])).trans
      exact congrArg (fun xs => (some tasks,xs)) (List.append_assoc acc [11] _)
termination_by sizeOf φ

theorem scannerInvariant : Comparators.GorbowSubstitutionCode.ScannerInvariant := ⟨termScan,formulaScan⟩

private theorem termEncode (n m : Nat) (σ : Fin n → Term m) (t : Term n) :
    substituteTermCode n m (dictionary σ) (GorbowTermPrefixCode.encode t) =
      some (GorbowTermPrefixCode.encode (GorbowSubstitution.substitute σ t)) := by
  have hv : validTerm n (GorbowTermPrefixCode.encode t) = true :=
    (GorbowSyntaxValidationProof.exactTypedDomain.1 n _).mpr
      ⟨t,(GorbowTermPrefixCodeProof.decoderExact n _ t).mpr rfl⟩
  have hr := congrArg Prod.snd (termScan n m 0 σ t [] [])
  simp only [liftN, List.nil_append, Nat.add_zero] at hr
  simp [substituteTermCode, hv, (GorbowLiftedDictionaryProof.dictionaryCalibration n m σ).2.1, subRaw, hr]

private theorem formulaEncode (n m : Nat) (σ : Fin n → Term m) (φ : Formula n) :
    substituteFormulaCode n m (dictionary σ) (GorbowFormulaPrefixCode.encode φ) =
      some (GorbowFormulaPrefixCode.encode (GorbowFormulaSubstitution.substituteFormula σ φ)) := by
  have hv : validFormula n (GorbowFormulaPrefixCode.encode φ) = true :=
    (GorbowSyntaxValidationProof.exactTypedDomain.2 n _).mpr
      ⟨φ,(GorbowFormulaPrefixCodeProof.decoderExact n _ φ).mpr rfl⟩
  have hr := congrArg Prod.snd (formulaScan n m 0 σ φ [] [])
  simp only [liftN, List.nil_append, Nat.add_zero] at hr
  simp [substituteFormulaCode, hv, (GorbowLiftedDictionaryProof.dictionaryCalibration n m σ).2.1, subRaw, hr]

theorem exactOutput : Comparators.GorbowSubstitutionCode.ExactOutput := by
  constructor
  · intro n m dict raw out
    constructor
    · intro h
      have hg : validTerm n raw = true ∧ dictionaryValid n m dict = true := by
        by_cases hv : validTerm n raw = true
        · by_cases hd : dictionaryValid n m dict = true
          · exact ⟨hv,hd⟩
          · simp [substituteTermCode,hv,hd] at h
        · simp [substituteTermCode,hv] at h
      obtain ⟨σ,rfl⟩ := (GorbowLiftedDictionaryProof.exactDictionaryDomain n m dict).mp hg.2
      obtain ⟨t,ht⟩ := (GorbowSyntaxValidationProof.exactTypedDomain.1 n raw).mp hg.1
      have he := (GorbowTermPrefixCodeProof.decoderExact n raw t).mp ht
      subst raw
      rw [termEncode] at h
      exact ⟨σ,t,rfl,rfl,(Option.some.inj h).symm⟩
    · rintro ⟨σ,t,rfl,rfl,rfl⟩
      exact termEncode n m σ t
  · intro n m dict raw out
    constructor
    · intro h
      have hg : validFormula n raw = true ∧ dictionaryValid n m dict = true := by
        by_cases hv : validFormula n raw = true
        · by_cases hd : dictionaryValid n m dict = true
          · exact ⟨hv,hd⟩
          · simp [substituteFormulaCode,hv,hd] at h
        · simp [substituteFormulaCode,hv] at h
      obtain ⟨σ,rfl⟩ := (GorbowLiftedDictionaryProof.exactDictionaryDomain n m dict).mp hg.2
      obtain ⟨φ,ht⟩ := (GorbowSyntaxValidationProof.exactTypedDomain.2 n raw).mp hg.1
      have he := (GorbowFormulaPrefixCodeProof.decoderExact n raw φ).mp ht
      subst raw
      rw [formulaEncode] at h
      exact ⟨σ,φ,rfl,rfl,(Option.some.inj h).symm⟩
    · rintro ⟨σ,φ,rfl,rfl,rfl⟩
      exact formulaEncode n m σ φ

theorem exactRejection : Comparators.GorbowSubstitutionCode.ExactRejection := by
  constructor
  · intro n m dict raw
    constructor
    · intro h
      rintro ⟨σ,t,rfl,rfl⟩
      rw [termEncode] at h
      cases h
    · intro h
      cases ho : substituteTermCode n m dict raw with
      | none => rfl
      | some out =>
          obtain ⟨σ,t,hd,hr,_⟩ := (exactOutput.1 n m dict raw out).mp ho
          exact False.elim (h ⟨σ,t,hd,hr⟩)
  · intro n m dict raw
    constructor
    · intro h
      rintro ⟨σ,φ,rfl,rfl⟩
      rw [formulaEncode] at h
      cases h
    · intro h
      cases ho : substituteFormulaCode n m dict raw with
      | none => rfl
      | some out =>
          obtain ⟨σ,φ,hd,hr,_⟩ := (exactOutput.2 n m dict raw out).mp ho
          exact False.elim (h ⟨σ,φ,hd,hr⟩)

theorem realization : Comparators.GorbowSubstitutionCode.Realization := by
  constructor
  · intro n m σ t I v
    exact ⟨_,termEncode n m σ t,GorbowSubstitution.substitute_realize I v σ t⟩
  · intro n m σ φ I v
    exact ⟨_,formulaEncode n m σ φ,GorbowFormulaSubstitution.substituteFormula_realize φ I v σ⟩
private abbrev Config := Nat × Nat × List (List Nat)

private theorem pr_emitList : Primrec (fun p : (Config × Nat) × List Task =>
    match p.2 with
    | [] => [p.1.2]
    | task :: _ =>
        if task.1 = 2 then liftedCode p.1.1.2.1 (task.2-p.1.1.1) p.1.1.2.2 p.1.2
        else if task.1 = 0 ∧ p.1.2 = 0 then [] else [p.1.2]) := by
  have hc : Primrec (fun p : ((Config × Nat) × List Task) × (Task × List Task) => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hx : Primrec (fun p : ((Config × Nat) × List Task) × (Task × List Task) => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have ht : Primrec (fun p : ((Config × Nat) × List Task) × (Task × List Task) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hn := Primrec.fst.comp hc
  have hm := Primrec.fst.comp (Primrec.snd.comp hc)
  have hd := Primrec.snd.comp (Primrec.snd.comp hc)
  have hk := Primrec.fst.comp ht
  have hcontext := Primrec.snd.comp ht
  have hlift := GorbowLiftedDictionaryProof.uniformPrograms.2.comp
    (hm.pair ((Primrec.nat_sub.comp hcontext hn).pair (hd.pair hx)))
  have hsingle := Primrec.list_cons.comp hx (Primrec.const [])
  have hbranch := Primrec.ite (Primrec.eq.comp hk (Primrec.const 2)) hlift
    (Primrec.ite ((Primrec.eq.comp hk (Primrec.const 0)).and (Primrec.eq.comp hx (Primrec.const 0)))
      (Primrec.const []) hsingle)
  have h := Primrec.list_casesOn Primrec.snd
    (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) (Primrec.const [])) hbranch.to₂
  apply h.of_eq
  intro p
  cases p.2 <;> rfl

private theorem pr_emitPacked : Primrec (fun p : Config × State × Nat => emit p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2) := by
  have h := Primrec.option_casesOn (Primrec.fst.comp Primrec.snd : Primrec (fun p : Config × State × Nat => p.2.1))
    (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const []))
    (pr_emitList.comp (((Primrec.fst.comp Primrec.fst).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd)).to₂
  apply h.of_eq
  intro p
  rcases p with ⟨c,state,token⟩
  cases state with
  | none => rfl
  | some tasks => cases tasks <;> rfl

private theorem pr_emit : Primrec (fun p : Nat × Nat × List (List Nat) × State × Nat => emit p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  have hn : Primrec (fun p : Nat × Nat × List (List Nat) × State × Nat => p.1) := Primrec.fst
  have hm : Primrec (fun p : Nat × Nat × List (List Nat) × State × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : Nat × Nat × List (List Nat) × State × Nat => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hsx : Primrec (fun p : Nat × Nat × List (List Nat) × State × Nat => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact pr_emitPacked.comp ((hn.pair (hm.pair hd)).pair hsx)

private theorem pr_subStep : Primrec (fun p : Nat × Nat × List (List Nat) × OutputState × Nat => subStep p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  have hn : Primrec (fun p : Nat × Nat × List (List Nat) × OutputState × Nat => p.1) := Primrec.fst
  have hm : Primrec (fun p : Nat × Nat × List (List Nat) × OutputState × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : Nat × Nat × List (List Nat) × OutputState × Nat => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hos : Primrec (fun p : Nat × Nat × List (List Nat) × OutputState × Nat => p.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hx : Primrec (fun p : Nat × Nat × List (List Nat) × OutputState × Nat => p.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hs := Primrec.fst.comp hos
  have ho := Primrec.snd.comp hos
  exact (GorbowSyntaxValidationProof.uniformPrograms.2.1.comp (hs.pair hx)).pair
    (Primrec.list_append.comp ho (pr_emit.comp (hn.pair (hm.pair (hd.pair (hs.pair hx))))))

private abbrev RawInput := Nat × Nat × Nat × List (List Nat) × List Nat

private theorem pr_rawInitial : Primrec (fun p : RawInput => (some [(p.1,p.2.1)],([] : List Nat))) :=
  (Primrec.option_some.comp (Primrec.list_cons.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))
    (Primrec.const []))).pair (Primrec.const [])

private theorem pr_rawArguments : Primrec (fun p : RawInput × OutputState × Nat =>
    (p.1.2.1,p.1.2.2.1,p.1.2.2.2.1,p.2.1,p.2.2)) := by
  have hn : Primrec (fun p : RawInput => p.2.1) := Primrec.fst.comp Primrec.snd
  have hm : Primrec (fun p : RawInput => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hd : Primrec (fun p : RawInput => p.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact (hn.comp Primrec.fst).pair ((hm.comp Primrec.fst).pair
    ((hd.comp Primrec.fst).pair Primrec.snd))

private theorem pr_rawStep : Primrec (fun p : RawInput × OutputState × Nat =>
    subStep p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.2.1 p.2.2) := by
  have h := pr_subStep.comp pr_rawArguments
  exact h.of_eq (fun _ => rfl)

private theorem pr_rawTokens : Primrec (fun p : RawInput => p.2.2.2.2) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

private theorem pr_rawFold : Primrec (fun p : RawInput =>
    p.2.2.2.2.foldl (subStep p.2.1 p.2.2.1 p.2.2.2.1) (some [(p.1,p.2.1)],[])) := by
  have h := Primrec.list_foldl pr_rawTokens pr_rawInitial pr_rawStep.to₂
  exact h.of_eq (fun _ => rfl)

private theorem pr_subRaw : Primrec (fun p : RawInput => subRaw p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) :=
  Primrec.snd.comp pr_rawFold

private theorem pr_subCode (kind : Nat) (valid : Nat → List Nat → Bool)
    (hv : Primrec (fun p : Nat × List Nat => valid p.1 p.2)) :
    Primrec (fun p : Nat × Nat × List (List Nat) × List Nat =>
      if valid p.1 p.2.2.2 && dictionaryValid p.1 p.2.1 p.2.2.1 then
        some (subRaw kind p.1 p.2.1 p.2.2.1 p.2.2.2) else none) := by
  have hn : Primrec (fun p : Nat × Nat × List (List Nat) × List Nat => p.1) := Primrec.fst
  have hm : Primrec (fun p : Nat × Nat × List (List Nat) × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : Nat × Nat × List (List Nat) × List Nat => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hl : Primrec (fun p : Nat × Nat × List (List Nat) × List Nat => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hg := Primrec.and.comp (hv.comp (hn.pair hl))
    (GorbowLiftedDictionaryProof.uniformPrograms.1.comp (hn.pair (hm.pair hd)))
  exact Primrec.ite (Primrec.eq.comp hg (Primrec.const true))
    (Primrec.option_some.comp (pr_subRaw.comp ((Primrec.const kind).pair Primrec.id))) (Primrec.const none)

theorem uniformPrograms : Comparators.GorbowSubstitutionCode.UniformPrograms :=
  ⟨pr_emit,pr_subStep,pr_subRaw,
    pr_subCode 0 validTerm GorbowSyntaxValidationProof.uniformPrograms.2.2.2.1,
    pr_subCode 1 validFormula GorbowSyntaxValidationProof.uniformPrograms.2.2.2.2⟩

theorem gorbowSubstitutionCode : Comparators.GorbowSubstitutionCode.Target :=
  ⟨scannerInvariant,exactOutput,exactRejection,realization,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowSubstitutionCodeProof
