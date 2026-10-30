module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowNamedBindingCode
public import LogicLineages.ComputabilityKnowledge.GorbowNamedBindingProof
public import LogicLineages.ComputabilityKnowledge.GorbowSubstitutionCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowSupportCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructorsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedBindingCodeProof
open GorbowSyntax GorbowFreeSupport GorbowNamedBinding GorbowNamedBindingCode
open GorbowLiftedDictionary GorbowCodeConstructors GorbowSubstitutionCode

theorem dictionaryCalibration : Comparators.GorbowNamedBindingCode.DictionaryCalibration := by
  intro n v
  constructor <;> apply List.ext_getElem
  · simp [bindDictionaryCode,dictionary]
  · intro i hi hj
    by_cases he : i=v.val <;> simp [bindDictionaryCode,dictionary,bindDictionary,GorbowTermPrefixCode.encode,variableCode,Fin.ext_iff,he]
  · simp [selectDictionaryCode,dictionary]
  · intro i hi hj
    by_cases he : i=v.val <;> simp [selectDictionaryCode,dictionary,selectDictionary,GorbowTermPrefixCode.encode,variableCode,Fin.ext_iff,he]

private theorem bindEncoded (n : Nat) (v : Fin n) (φ : Formula n) :
    bindAllCode n v.val (GorbowFormulaPrefixCode.encode φ)=some (GorbowFormulaPrefixCode.encode (bindAll v φ)) ∧
    bindExCode n v.val (GorbowFormulaPrefixCode.encode φ)=some (GorbowFormulaPrefixCode.encode (bindEx v φ)) := by
  have hs := (GorbowSubstitutionCodeProof.exactOutput.2 n (n+1) _ _ _).mpr
    ⟨bindDictionary v,φ,(dictionaryCalibration n v).1,rfl,rfl⟩
  simp [bindAllCode,bindExCode,bindCode,v.isLt,hs,bindAll,bindEx,GorbowFormulaPrefixCode.encode,unary]

private theorem bindDomain (tag n v : Nat) (raw out : List Nat) (h : bindCode tag n v raw=some out) :
    ∃ (hv : v<n) (φ : Formula n), raw=GorbowFormulaPrefixCode.encode φ := by
  unfold bindCode at h
  split at h
  · rename_i hv
    cases hs : substituteFormulaCode n (n+1) (bindDictionaryCode n v) raw with
    | none => simp [hs] at h
    | some a =>
      obtain ⟨σ,φ,hd,hr,ho⟩ := (GorbowSubstitutionCodeProof.exactOutput.2 _ _ _ _ _).mp hs
      exact ⟨hv,φ,hr⟩
  · simp at h

theorem exactBinding : Comparators.GorbowNamedBindingCode.ExactBinding := by
  intro n v raw out
  constructor
  · constructor
    · intro h
      obtain ⟨hv,φ,rfl⟩ := bindDomain 10 n v raw out h
      rw [(bindEncoded n ⟨v,hv⟩ φ).1] at h
      exact ⟨hv,φ,rfl,(Option.some.inj h).symm⟩
    · rintro ⟨hv,φ,rfl,rfl⟩
      exact (bindEncoded n ⟨v,hv⟩ φ).1
  · constructor
    · intro h
      obtain ⟨hv,φ,rfl⟩ := bindDomain 11 n v raw out h
      rw [(bindEncoded n ⟨v,hv⟩ φ).2] at h
      exact ⟨hv,φ,rfl,(Option.some.inj h).symm⟩
    · rintro ⟨hv,φ,rfl,rfl⟩
      exact (bindEncoded n ⟨v,hv⟩ φ).2

private theorem rangeSingleton (n v : Nat) (hv : v<n) :
    (List.range n).filter (fun i => decide (i=v))=[v] := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : v=n
    · subst v
      simp [List.range_succ,List.filter_eq_nil_iff]
      omega
    · have hvn : v<n := by omega
      simp [List.range_succ,ih hvn,he,Ne.symm he]

private theorem namesSingleton (n : Nat) (v : Fin n) (φ : Formula n) :
    GorbowSupportCode.formulaNames n (GorbowFormulaPrefixCode.encode φ)=some [v.val] ↔ formulaSupport φ={v.val} := by
  rw [GorbowSupportCodeProof.exactNames.2]
  constructor
  · rintro ⟨ψ,he,hn⟩
    have hp : φ=ψ := GorbowFormulaPrefixCodeProof.encodingInjective n he
    subst ψ
    apply Finset.ext
    intro i
    have hb := GorbowFreeSupportProof.supportBound.2 n φ i
    have hm := congrArg (fun xs : List Nat => i∈xs) hn
    simp only [List.mem_cons,List.not_mem_nil,or_false,List.mem_filter,List.mem_range,decide_eq_true_eq] at hm
    simpa only [Finset.mem_singleton] using ((Iff.of_eq hm).trans (and_iff_right_of_imp hb)).symm
  · intro hs
    refine ⟨φ,rfl,?_⟩
    simpa [hs] using (rangeSingleton n v.val v.isLt).symm

private theorem selectEncoded (n : Nat) (v : Fin n) (φ : Formula n) (hs : formulaSupport φ={v.val}) :
    selectCode n v.val (GorbowFormulaPrefixCode.encode φ)=some (GorbowFormulaPrefixCode.encode (selectVariable v φ)) := by
  rw [selectCode,if_pos ⟨v.isLt,(namesSingleton n v φ).mpr hs⟩]
  exact (GorbowSubstitutionCodeProof.exactOutput.2 n 1 _ _ _).mpr
    ⟨selectDictionary v,φ,(dictionaryCalibration n v).2,rfl,rfl⟩

theorem exactSelection : Comparators.GorbowNamedBindingCode.ExactSelection := by
  intro n v raw out
  constructor
  · intro h
    have hg : v<n ∧ GorbowSupportCode.formulaNames n raw=some [v] := by
      by_contra hg
      simp [selectCode,hg] at h
    obtain ⟨φ,hr,hn⟩ := (GorbowSupportCodeProof.exactNames.2 n raw [v]).mp hg.2
    subst raw
    have hs := (namesSingleton n ⟨v,hg.1⟩ φ).mp hg.2
    rw [selectEncoded n ⟨v,hg.1⟩ φ hs] at h
    exact ⟨hg.1,φ,rfl,hs,(Option.some.inj h).symm⟩
  · rintro ⟨hv,φ,rfl,hs,rfl⟩
    exact selectEncoded n ⟨v,hv⟩ φ hs

theorem selectedOutput : Comparators.GorbowNamedBindingCode.SelectedOutput := by
  intro n v raw out h
  obtain ⟨hv,φ,hr,hs,ho⟩ := (exactSelection n v raw out).mp h
  exact ⟨⟨selectVariable ⟨v,hv⟩ φ,(GorbowNamedBindingProof.selectionSupport n ⟨v,hv⟩ φ hs).2⟩,ho⟩

private theorem invalidEncoded (n : Nat) (φ : Formula n) :
    GorbowSyntaxValidation.validFormula n (GorbowFormulaPrefixCode.encode φ)=true :=
  (GorbowSyntaxValidationProof.exactTypedDomain.2 n _).mpr
    ⟨φ,(GorbowFormulaPrefixCodeProof.decoderExact n _ φ).mpr rfl⟩

theorem malformedRejection : Comparators.GorbowNamedBindingCode.MalformedRejection := by
  intro n v raw h
  have hn : ∀ (hv : v<n) (φ : Formula n), raw ≠ GorbowFormulaPrefixCode.encode φ := by
    intro hv φ hr
    rcases h with h | h
    · exact (h hv).elim
    · subst raw
      rw [invalidEncoded] at h
      contradiction
  constructor
  · cases he : bindAllCode n v raw with
    | none => rfl
    | some out =>
      obtain ⟨hv,φ,hr,ho⟩ := (exactBinding n v raw out).1.mp he
      exact (hn hv φ hr).elim
  constructor
  · cases he : bindExCode n v raw with
    | none => rfl
    | some out =>
      obtain ⟨hv,φ,hr,ho⟩ := (exactBinding n v raw out).2.mp he
      exact (hn hv φ hr).elim
  · cases he : selectCode n v raw with
    | none => rfl
    | some out =>
      obtain ⟨hv,φ,hr,hs,ho⟩ := (exactSelection n v raw out).mp he
      exact (hn hv φ hr).elim

private theorem pr_bindDictionary : Primrec (fun p : Nat × Nat => bindDictionaryCode p.1 p.2) := by
  have he : PrimrecPred (fun p : (Nat × Nat) × Nat => p.2=p.1.2) :=
    Primrec.eq.comp Primrec.snd (Primrec.snd.comp Primrec.fst)
  exact Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (Primrec.ite he (Primrec.const (variableCode 0))
      (GorbowCodeConstructorsProof.uniformPrograms.1.comp (Primrec.succ.comp Primrec.snd))).to₂
private theorem pr_selectDictionary : Primrec (fun p : Nat × Nat => selectDictionaryCode p.1 p.2) := by
  have he : PrimrecPred (fun p : (Nat × Nat) × Nat => p.2=p.1.2) :=
    Primrec.eq.comp Primrec.snd (Primrec.snd.comp Primrec.fst)
  exact Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (Primrec.ite he (Primrec.const (variableCode 0)) (Primrec.const [1])).to₂
private theorem pr_bind (tag : Nat) : Primrec (fun p : Nat × Nat × List Nat => bindCode tag p.1 p.2.1 p.2.2) := by
  have hn : Primrec (fun p : Nat × Nat × List Nat => p.1) := Primrec.fst
  have hv : Primrec (fun p : Nat × Nat × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr : Primrec (fun p : Nat × Nat × List Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hs := GorbowSubstitutionCodeProof.uniformPrograms.2.2.2.2.comp
    (hn.pair ((Primrec.succ.comp hn).pair ((pr_bindDictionary.comp (hn.pair hv)).pair hr)))
  have hm := Primrec.option_map hs
    (GorbowCodeConstructorsProof.uniformPrograms.2.1.comp ((Primrec.const tag).pair Primrec.snd)).to₂
  exact Primrec.ite (Primrec.nat_lt.comp hv hn) hm (Primrec.const none)
private theorem pr_select : Primrec (fun p : Nat × Nat × List Nat => selectCode p.1 p.2.1 p.2.2) := by
  have hn : Primrec (fun p : Nat × Nat × List Nat => p.1) := Primrec.fst
  have hv : Primrec (fun p : Nat × Nat × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr : Primrec (fun p : Nat × Nat × List Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have names := GorbowSupportCodeProof.uniformPrograms.2.2.2.2.1.comp (hn.pair hr)
  have wanted := Primrec.option_some.comp (Primrec.list_cons.comp hv (Primrec.const []))
  have hs := GorbowSubstitutionCodeProof.uniformPrograms.2.2.2.2.comp
    (hn.pair ((Primrec.const 1).pair ((pr_selectDictionary.comp (hn.pair hv)).pair hr)))
  exact Primrec.ite ((Primrec.nat_lt.comp hv hn).and (Primrec.eq.comp names wanted)) hs (Primrec.const none)

theorem uniformPrograms : Comparators.GorbowNamedBindingCode.UniformPrograms :=
  ⟨pr_bindDictionary,pr_selectDictionary,pr_bind 10,pr_bind 11,pr_select⟩
theorem gorbowNamedBindingCode : Comparators.GorbowNamedBindingCode.Target :=
  ⟨dictionaryCalibration,exactBinding,exactSelection,selectedOutput,malformedRejection,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowNamedBindingCodeProof
