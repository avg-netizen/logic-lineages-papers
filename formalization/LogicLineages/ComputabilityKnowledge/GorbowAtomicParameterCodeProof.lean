module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowAtomicParameterCode
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryTermCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedSyntaxCodeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowAtomicParameterCodeProof
open GorbowSyntax GorbowAtomicParameters GorbowNameDictionary GorbowAtomicParameterCode
open GorbowCodeConstructors GorbowRegistryTermCode

theorem slotCalibration : Comparators.GorbowAtomicParameterCode.SlotCalibration := by
  intro n m names i
  have hl : (namesList names).length=n := by simp [namesList]
  by_cases hk : (namesList names).idxOf i.val<n
  · constructor
    · simp [codeSlot,hl,hk,codeDictionary,List.getD_eq_getElem?_getD,GorbowTermPrefixCode.encode,variableCode]
    · simp only [valueSlot,hl,hk,ite_true,valueDictionary,GorbowNameDictionary.dictionary]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hk,dif_pos,Option.getD_some]
      exact GorbowRegistryTermCodeProof.evaluationCalibration n (.var ⟨_,hk⟩)
  · constructor
    · simp only [codeSlot,hl,hk,ite_false,codeDictionary,List.getD_eq_getElem?_getD,
        List.getElem?_ofFn,hk,dif_neg,Option.getD_none]
      exact (GorbowCodeConstructorsProof.numeralCalibration n _).symm
    · simp [valueSlot,hl,hk,valueDictionary,GorbowNameDictionary.dictionary,
        List.getD_eq_getElem?_getD,GorbowTermPrefixCode.encode]

theorem dictionaryCalibration : Comparators.GorbowAtomicParameterCode.DictionaryCalibration := by
  intro n m names
  constructor
  · apply List.ext_getElem
    · simp [codeSlots]
    · intro i hi hj
      have hib : i<m := by simpa [codeSlots] using hi
      simpa [codeSlots] using (slotCalibration n m names ⟨i,hib⟩).1
  · apply List.ext_getElem
    · simp [valueSlots,GorbowLiftedDictionary.dictionary]
    · intro i hi hj
      have hib : i<m := by simpa [valueSlots] using hi
      simpa [valueSlots,GorbowLiftedDictionary.dictionary] using (slotCalibration n m names ⟨i,hib⟩).2

theorem instanceCalibration : Comparators.GorbowAtomicParameterCode.InstanceCalibration := by
  intro n m R names
  have ht := GorbowRegistryTermCodeProof.tupleCalibration n (List.ofFn (codeDictionary names))
  simp only [List.map_ofFn,Function.comp_def] at ht
  rw [← (dictionaryCalibration n m names).1] at ht
  have hh := GorbowRegistryTermCodeProof.headerCalibration n 3 1
    [Term.numeral m,GorbowSortedSyntaxCode.formulaQuote n R,argumentTuple names]
  simp only [List.map_cons,List.map_nil,GorbowSortedSyntaxCode.formulaQuote] at hh
  rw [GorbowCodeConstructorsProof.numeralCalibration n m,
    GorbowCodeConstructorsProof.numeralCalibration n (GorbowSortedSyntaxCode.formulaCode R)] at hh
  change headerRaw 3 1 [numeral m,numeral (GorbowSortedSyntaxCode.formulaRawNumber (GorbowFormulaPrefixCode.encode R)),
    GorbowTermPrefixCode.encode (GorbowRegistryTuple.tupleTerm (List.ofFn (codeDictionary names)))]=_ at hh
  rw [← ht] at hh
  exact congrArg (List.cons 5) hh

private theorem pr_index : Primrec (fun p : List Nat × Nat => p.1.idxOf p.2) :=
  Primrec.list_idxOf.comp Primrec.snd Primrec.fst
private theorem pr_codeSlot : Primrec (fun p : List Nat × Nat => codeSlot p.1 p.2) :=
  Primrec.ite (Primrec.nat_lt.comp pr_index (Primrec.list_length.comp Primrec.fst))
    (GorbowCodeConstructorsProof.uniformPrograms.1.comp pr_index) (Primrec.const _)
private theorem pr_valueSlot : Primrec (fun p : List Nat × Nat => valueSlot p.1 p.2) :=
  Primrec.ite (Primrec.nat_lt.comp pr_index (Primrec.list_length.comp Primrec.fst))
    (GorbowRegistryTermCodeProof.uniformPrograms.2.2.2.1.comp
      (GorbowCodeConstructorsProof.uniformPrograms.1.comp pr_index)) (Primrec.const [1])
private theorem pr_codeSlots : Primrec (fun p : Nat × List Nat => codeSlots p.1 p.2) :=
  Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (pr_codeSlot.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂
private theorem pr_valueSlots : Primrec (fun p : Nat × List Nat => valueSlots p.1 p.2) :=
  Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (pr_valueSlot.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂
private theorem pr_instance : Primrec (fun p : Nat × List Nat × List Nat => instanceRaw p.1 p.2.1 p.2.2) := by
  have hn := GorbowCodeConstructorsProof.uniformPrograms.2.2.2.1
  have hraw : Primrec (fun p : Nat × List Nat × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hnames : Primrec (fun p : Nat × List Nat × List Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have htuple := GorbowRegistryTermCodeProof.uniformPrograms.2.1.comp
    (pr_codeSlots.comp (Primrec.fst.pair hnames))
  have hargs := Primrec.list_cons.comp (hn.comp Primrec.fst)
    (Primrec.list_cons.comp (hn.comp (GorbowSortedSyntaxCodeProof.uniformPrograms.2.2.1.comp hraw))
      (Primrec.list_cons.comp htuple (Primrec.const [])))
  exact Primrec.list_cons.comp (Primrec.const 5)
    (GorbowRegistryTermCodeProof.uniformPrograms.2.2.1.comp
      ((Primrec.const 3).pair ((Primrec.const 1).pair hargs)))

theorem uniformPrograms : Comparators.GorbowAtomicParameterCode.UniformPrograms :=
  ⟨pr_codeSlot,pr_valueSlot,pr_codeSlots,pr_valueSlots,pr_instance⟩
theorem gorbowAtomicParameterCode : Comparators.GorbowAtomicParameterCode.Target :=
  ⟨slotCalibration,dictionaryCalibration,instanceCalibration,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowAtomicParameterCodeProof
