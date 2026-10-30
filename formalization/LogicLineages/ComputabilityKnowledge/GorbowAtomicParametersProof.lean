module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowAtomicParameters
public import LogicLineages.ComputabilityKnowledge.GorbowAtomicRegistryProof
public import LogicLineages.ComputabilityKnowledge.GorbowNameDictionaryProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowAtomicParametersProof
open GorbowSyntax GorbowStandardInstances GorbowSortedSyntaxCode GorbowSortedRevision GorbowRegistryTuple
open GorbowAtomicParameters

private theorem headerRealize {n : Nat} (arity tag : Nat) (as : List (Term n)) I ρ :
    (headerTerm arity tag as).realize I ρ=header arity tag (as.map (fun t => t.realize I ρ)) :=
  (GorbowRegistryTupleProof.termCalibration n I ρ).2.2 arity tag as

theorem guardCalibration : Comparators.GorbowAtomicParameters.GuardCalibration := by
  intro n t P ρ
  change GorbowAtomicRegistry.ground.universalRelation ((headerTerm 1 2 [t]).realize _ ρ) ↔ _
  rw [headerRealize]
  simp only [List.map_cons,List.map_nil]
  exact (GorbowAtomicRegistryProof.originalDispatch.1 (t.realize _ ρ) 0).2.2.1

attribute [local irreducible] headerTerm pairTerm tupleTerm

theorem closureSemantics : Comparators.GorbowAtomicParameters.ClosureSemantics := by
  intro n
  induction n with
  | zero =>
    intro φ P
    constructor
    · intro h ρ _
      have he : ρ=Fin.elim0 := by funext i; exact Fin.elim0 i
      rw [he]; exact h
    · intro h; exact h Fin.elim0 (fun i => Fin.elim0 i)
  | succ n ih =>
    intro φ P
    change (arithmeticClosure (Formula.all (.imp (GorbowSortedQuantifierTruth.arithmeticTermGuard (.var 0)) φ))).realize _ _ ↔ _
    rw [ih]
    constructor
    · intro h ρ hρ
      have he : Fin.cases (ρ 0) (fun i : Fin n => ρ i.succ)=ρ := by
        funext i; exact Fin.cases rfl (fun _ => rfl) i
      have hv := h (fun i : Fin n => ρ i.succ) (fun i => hρ i.succ) (ρ 0)
      have hg : (GorbowSortedQuantifierTruth.arithmeticTermGuard (.var 0)).realize
          (interpretation GorbowAtomicRegistry.ground P) (Fin.cases (ρ 0) (fun i : Fin n => ρ i.succ)) :=
        (guardCalibration (n+1) (.var 0) P _).mpr (hρ 0)
      have hx := hv hg
      rw [he] at hx
      exact hx
    · intro h ρ hρ x hx
      apply h (Fin.cases x ρ)
      intro i
      refine Fin.cases ?_ (fun j => hρ j) i
      exact (guardCalibration (n+1) (.var 0) P (Fin.cases x ρ)).mp hx

theorem evaluationCalibration : Comparators.GorbowAtomicParameters.EvaluationCalibration := by
  intro n t P ρ s hs ht
  change GorbowAtomicRegistry.functionProgram ((headerTerm 1 1 [t]).realize _ ρ)=_
  rw [headerRealize]
  simp only [List.map_cons,List.map_nil,ht]
  exact GorbowAtomicRegistryProof.actualCalibration.1 s hs _

private theorem indexAt {n m : Nat} (names : Fin n → Fin m) (hn : Function.Injective names) (j : Fin n) :
    (GorbowNameDictionary.namesList names).idxOf (names j).val=j.val := by
  have hi : Function.Injective (fun j => (names j).val) := Fin.val_injective.comp hn
  have hl : (GorbowNameDictionary.namesList names).Nodup := List.nodup_ofFn.mpr hi
  have he := hl.idxOf_getElem j.val (by simp [GorbowNameDictionary.namesList,j.isLt])
  simpa [GorbowNameDictionary.namesList] using he

private theorem codeLookup {n m : Nat} (names : Fin n → Fin m) (hn : Function.Injective names) (j : Fin n) :
    codeDictionary names (names j)=.var j := by
  simp [codeDictionary,indexAt names hn j,List.getD_eq_getElem?_getD,j.isLt]
private theorem codeUnused {n m : Nat} (names : Fin n → Fin m) (i : Fin m)
    (hi : ¬∃ j,names j=i) : codeDictionary names i=Term.numeral (termCode (.zero : Term 0)) := by
  have hm : i.val∉GorbowNameDictionary.namesList names := by
    simp only [GorbowNameDictionary.namesList,List.mem_ofFn]
    rintro ⟨j,hj⟩; exact hi ⟨j,Fin.ext hj⟩
  have hh := List.idxOf_eq_length_iff.mpr hm
  unfold codeDictionary
  rw [hh]
  simp [GorbowNameDictionary.namesList,List.getD_eq_getElem?_getD]

theorem dictionaryCalibration : Comparators.GorbowAtomicParameters.DictionaryCalibration := by
  intro n m names hn ts hts P ρ hρ
  have hc : ∀ i, (codeDictionary names i).realize (interpretation GorbowAtomicRegistry.ground P) ρ=
      termCode (GorbowNameDictionary.dictionary names ts i) := by
    intro i
    by_cases hi : ∃ j,names j=i
    · obtain ⟨j,rfl⟩ := hi
      rw [codeLookup names hn j,GorbowNameDictionaryProof.lookup n m 0 names hn ts j]
      exact hρ j
    · rw [codeUnused names i hi,GorbowNameDictionaryProof.unusedZero n m 0 names ts i hi]
      exact numeral_realize _ _ _
  have hv : ∀ i, (valueDictionary names i).realize (interpretation GorbowAtomicRegistry.ground P) ρ=
      (GorbowNameDictionary.dictionary names ts i).realize (interpretation GorbowAtomicRegistry.ground P) Fin.elim0 := by
    intro i
    by_cases hi : ∃ j,names j=i
    · obtain ⟨j,rfl⟩ := hi
      change (GorbowNameDictionary.dictionary names (fun j => evaluationTerm (.var j)) (names j)).realize _ _=_
      rw [GorbowNameDictionaryProof.lookup n m n names hn _ j,GorbowNameDictionaryProof.lookup n m 0 names hn ts j]
      exact evaluationCalibration n (.var j) P ρ (ts j) (hts j) (hρ j)
    · change (GorbowNameDictionary.dictionary names (fun j => evaluationTerm (.var j)) i).realize _ _=_
      rw [GorbowNameDictionaryProof.unusedZero n m n names _ i hi,GorbowNameDictionaryProof.unusedZero n m 0 names ts i hi]
      rfl
  refine ⟨hc,hv,?_⟩
  rw [argumentTuple,(GorbowRegistryTupleProof.termCalibration n (interpretation GorbowAtomicRegistry.ground P) ρ).2.1]
  congr 1
  rw [List.map_ofFn]
  congr 1
  funext i
  exact hc i

theorem gorbowAtomicParameters : Comparators.GorbowAtomicParameters.Target :=
  ⟨guardCalibration,closureSemantics,evaluationCalibration,dictionaryCalibration⟩
end LogicLineages.ComputabilityKnowledge.GorbowAtomicParametersProof
