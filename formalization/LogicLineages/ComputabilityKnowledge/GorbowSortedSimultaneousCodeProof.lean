module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedSimultaneousCode
public import LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowSubstitutionCodeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSortedSimultaneousCodeProof
open GorbowSyntax GorbowSortedSyntaxCode GorbowSortedSimultaneousCode

private theorem fullAt (t : Term 0) : GorbowSortedBooleanCode.fullTermCode (termCode t)=true :=
  (GorbowSortedBooleanCodeProof.exactDomains.2.1 _).mpr ⟨t,rfl⟩
private theorem decodeAt (t : Term 0) : decodeTermRaw (termCode t)=some (GorbowTermPrefixCode.encode t) :=
  GorbowSortedSyntaxCodeProof.actualCalibration.2.2.1 0 t

theorem dictionaryCalibration : Comparators.GorbowSortedSimultaneousCode.DictionaryCalibration := by
  intro n σ
  constructor
  · simp [dictionaryOK,List.all_eq_true,fullAt]
  · simp [dictionaryRaw,GorbowLiftedDictionary.dictionary,List.map_ofFn,Function.comp_def,decodeAt]

theorem exactDictionary : Comparators.GorbowSortedSimultaneousCode.ExactDictionary := by
  intro n codes
  constructor
  · intro h
    have hh : codes.length=n ∧ codes.all GorbowSortedBooleanCode.fullTermCode=true := by
      simpa only [dictionaryOK,Bool.and_eq_true,decide_eq_true_eq] using h
    have ha := List.all_eq_true.mp hh.2
    have hex : ∀ i : Fin n, ∃ t : Term 0, codes[i.val]'(by omega)=termCode t := by
      intro i
      exact (GorbowSortedBooleanCodeProof.exactDomains.2.1 _).mp (ha _ (List.getElem_mem _))
    choose σ hσ using hex
    refine ⟨σ,?_⟩
    apply List.ext_getElem
    · simp [hh.1]
    · intro i hi hj
      simpa using hσ ⟨i,by omega⟩
  · rintro ⟨σ,rfl⟩
    exact (dictionaryCalibration n σ).1

theorem actualCalibration : Comparators.GorbowSortedSimultaneousCode.ActualCalibration := by
  intro n φ σ
  have hd := GorbowSortedSyntaxCodeProof.actualCalibration.2.1 n φ
  have hg := (dictionaryCalibration n σ).1
  have he := (dictionaryCalibration n σ).2
  have hs := (GorbowSubstitutionCodeProof.exactOutput.2 n 0 _ _ _).mpr ⟨σ,φ,rfl,rfl,rfl⟩
  simp only [substituteNumber,hd,hg,ite_true,he]
  change Option.map formulaRawNumber (GorbowSubstitutionCode.substituteFormulaCode n 0 (GorbowLiftedDictionary.dictionary σ) (GorbowFormulaPrefixCode.encode φ))=_
  rw [hs]
  rfl

theorem exactOutput : Comparators.GorbowSortedSimultaneousCode.ExactOutput := by
  intro n code codes out
  constructor
  · intro h
    cases hd : decodeFormulaRaw code with
    | none => simp [substituteNumber,hd] at h
    | some raw =>
      have hg : dictionaryOK n codes=true := by
        cases he : dictionaryOK n codes <;> simp_all [substituteNumber]
      obtain ⟨σ,hσ⟩ := (exactDictionary n codes).mp hg
      cases hs : GorbowSubstitutionCode.substituteFormulaCode n 0 (dictionaryRaw codes) raw with
      | none => simp [substituteNumber,hd,hg,hs] at h
      | some output =>
        obtain ⟨τ,φ,_,hφ,_⟩ := (GorbowSubstitutionCodeProof.exactOutput.2 n 0 _ _ _).mp hs
        have hc := (GorbowSortedSyntaxCodeProof.exactRawDecoding.1 code raw).mp hd
        have hc' : code=formulaCode φ := by
          simpa [hφ,formulaRawNumber,formulaCode,GorbowCodeConstructors.formulaNumber] using hc
        have hh := actualCalibration n φ σ
        rw [←hc',←hσ,h] at hh
        exact ⟨φ,σ,hc',hσ,Option.some.inj hh⟩
  · rintro ⟨φ,σ,rfl,rfl,rfl⟩
    exact actualCalibration n φ σ

theorem exactRejection : Comparators.GorbowSortedSimultaneousCode.ExactRejection := by
  intro n code codes
  classical
  constructor
  · intro h
    by_cases hg : dictionaryOK n codes=false
    · exact Or.inl hg
    · right
      rintro ⟨φ,hφ⟩
      have ht : dictionaryOK n codes=true := by cases he : dictionaryOK n codes <;> simp_all
      obtain ⟨σ,hσ⟩ := (exactDictionary n codes).mp ht
      have hh := actualCalibration n φ σ
      rw [←hφ,←hσ,h] at hh
      contradiction
  · intro h
    cases ho : substituteNumber n code codes with
    | none => rfl
    | some out =>
      obtain ⟨φ,σ,hφ,hσ,_⟩ := (exactOutput n code codes out).mp ho
      rcases h with hg | hn
      · have hh := (exactDictionary n codes).mpr ⟨σ,hσ⟩
        rw [hg] at hh
        contradiction
      · exact False.elim (hn ⟨φ,hφ⟩)

private theorem pr_decodeTerm : Primrec (fun code : Nat => (decodeTermRaw code).getD []) :=
  Primrec.option_getD.comp GorbowSortedSyntaxCodeProof.uniformPrograms.2.2.2.2.2.2.1 (Primrec.const [])
private theorem pr_dictionary : Primrec dictionaryRaw :=
  Primrec.list_map Primrec.id (pr_decodeTerm.comp Primrec.snd).to₂
private theorem pr_all : Primrec (fun codes : List Nat => codes.all GorbowSortedBooleanCode.fullTermCode) := by
  have hp : PrimrecRel (fun code : Nat => fun _ : Unit => GorbowSortedBooleanCode.fullTermCode code=true) :=
    Primrec.eq.comp (GorbowSortedBooleanCodeProof.uniformPrograms.2.2.2.1.comp Primrec.fst) (Primrec.const true)
  have h := hp.forall_mem_list.decide.comp Primrec.id (Primrec.const ())
  apply h.of_eq
  intro codes
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,List.all_eq_true,id_eq]
private theorem pr_ok : Primrec (fun p : Nat × List Nat => dictionaryOK p.1 p.2) :=
  Primrec.and.comp (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) Primrec.fst).decide
    (pr_all.comp Primrec.snd)
private theorem pr_some : Primrec (fun p : (Nat × Nat × List Nat) × List Nat =>
    if dictionaryOK p.1.1 p.1.2.2 then
      (GorbowSubstitutionCode.substituteFormulaCode p.1.1 0 (dictionaryRaw p.1.2.2) p.2).map formulaRawNumber
    else none) := by
  have hn : Primrec (fun p : (Nat × Nat × List Nat) × List Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have hc : Primrec (fun p : (Nat × Nat × List Nat) × List Nat => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hs := GorbowSubstitutionCodeProof.uniformPrograms.2.2.2.2.comp
    (hn.pair ((Primrec.const 0).pair ((pr_dictionary.comp hc).pair Primrec.snd)))
  have hm := Primrec.option_map hs (GorbowSortedSyntaxCodeProof.uniformPrograms.2.2.1.comp Primrec.snd).to₂
  exact Primrec.ite (Primrec.eq.comp (pr_ok.comp (hn.pair hc)) (Primrec.const true)) hm (Primrec.const none)
private theorem pr_substitute : Primrec (fun p : Nat × Nat × List Nat => substituteNumber p.1 p.2.1 p.2.2) :=
  Primrec.option_bind (GorbowSortedSyntaxCodeProof.uniformPrograms.2.2.2.2.2.1.comp (Primrec.fst.comp Primrec.snd)) pr_some.to₂

theorem uniformPrograms : Comparators.GorbowSortedSimultaneousCode.UniformPrograms :=
  ⟨pr_dictionary,pr_ok,pr_substitute⟩
theorem gorbowSortedSimultaneousCode : Comparators.GorbowSortedSimultaneousCode.Target :=
  ⟨dictionaryCalibration,exactDictionary,exactOutput,actualCalibration,exactRejection,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowSortedSimultaneousCodeProof
