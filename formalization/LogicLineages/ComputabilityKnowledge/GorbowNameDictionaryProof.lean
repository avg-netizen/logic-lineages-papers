module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowNameDictionary
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaCompositionProof
public import LogicLineages.ComputabilityKnowledge.GorbowFreeSupportProof
public import Mathlib.Data.List.FinRange

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowNameDictionaryProof
open GorbowSyntax GorbowFreeSupport GorbowNameDictionary

private theorem indexAt {n m : Nat} (names : Fin n → Fin m) (hn : Function.Injective names) (j : Fin n) :
    (namesList names).idxOf (names j).val=j.val := by
  have hi : Function.Injective (fun j => (names j).val) := Fin.val_injective.comp hn
  have hl : (namesList names).Nodup := List.nodup_ofFn.mpr hi
  have he := hl.idxOf_getElem j.val (by simp [namesList,j.isLt])
  simpa [namesList] using he

theorem lookup : Comparators.GorbowNameDictionary.Lookup := by
  intro n m k names hn values j
  simp [dictionary,indexAt names hn j,List.getD_eq_getElem?_getD,j.isLt]

theorem unusedZero : Comparators.GorbowNameDictionary.UnusedZero := by
  intro n m k names values i hi
  have hm : i.val ∉ namesList names := by
    simp only [namesList,List.mem_ofFn]
    rintro ⟨j,hj⟩
    exact hi ⟨j,Fin.ext hj⟩
  have hh := List.idxOf_eq_length_iff.mpr hm
  unfold dictionary
  rw [hh]
  simp [namesList,List.getD_eq_getElem?_getD]

theorem preciseSupport : Comparators.GorbowNameDictionary.PreciseSupport := by
  intro n m R names hn hc
  have hi : Function.Injective (fun j => (names j).val) := Fin.val_injective.comp hn
  change formulaSupport R=Finset.univ.image (fun j => (names j).val) at hc
  constructor
  · rw [hc,Finset.card_image_of_injective _ hi]
    simp
  · intro i
    rw [hc]
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨j,hj⟩; exact ⟨j,Fin.ext hj⟩
    · rintro ⟨j,hj⟩; exact ⟨j,congrArg Fin.val hj⟩

theorem literalLocality : Comparators.GorbowNameDictionary.LiteralLocality := by
  intro n m k R names hn hc values σ hσ
  apply GorbowFormulaCompositionProof.occurrenceLocality m k R
  intro i hi
  obtain ⟨j,rfl⟩ := ((preciseSupport n m R names hn hc).2 i).mp hi
  exact (lookup n m k names hn values j).trans (hσ j).symm

theorem realization : Comparators.GorbowNameDictionary.Realization := by
  intro n m k R names hn hc values I ρ v hv
  rw [GorbowFormulaSubstitution.substituteFormula_realize]
  apply GorbowFreeSupportProof.semanticLocality.2 m R I
  intro i hi
  obtain ⟨j,rfl⟩ := ((preciseSupport n m R names hn hc).2 i).mp hi
  rw [lookup n m k names hn values j]
  exact (hv j).symm

theorem gorbowNameDictionary : Comparators.GorbowNameDictionary.Target :=
  ⟨lookup,unusedZero,preciseSupport,literalLocality,realization⟩
end LogicLineages.ComputabilityKnowledge.GorbowNameDictionaryProof
