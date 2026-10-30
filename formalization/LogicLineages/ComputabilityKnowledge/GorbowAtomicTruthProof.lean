module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowAtomicTruth
public import LogicLineages.ComputabilityKnowledge.GorbowAtomicParametersProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowAtomicTruthProof
open GorbowSyntax GorbowStandardInstances GorbowSortedSyntaxCode GorbowSortedRevision GorbowRegistryTuple
open GorbowAtomicParameters GorbowAtomicTruth GorbowRevisionComposition GorbowFormulaSubstitution

theorem codeCalibration : Comparators.GorbowAtomicTruth.CodeCalibration := by
  intro n m R names hn ts hts P ρ hρ
  have ht := (GorbowAtomicParametersProof.dictionaryCalibration n m names hn ts hts P ρ hρ).2.2
  change GorbowAtomicRegistry.functionProgram ((headerTerm 3 1 [Term.numeral m,formulaQuote n R,argumentTuple names]).realize _ ρ)=_
  rw [(GorbowRegistryTupleProof.termCalibration n (interpretation GorbowAtomicRegistry.ground P) ρ).2.2]
  simp only [List.map_cons,List.map_nil,formulaQuote,numeral_realize,ht]
  exact GorbowAtomicRegistryProof.actualCalibration.2 m R (GorbowNameDictionary.dictionary names ts)

attribute [local irreducible] headerTerm pairTerm tupleTerm

private theorem bodyRealization {n m : Nat} (R : Formula m) (names : Fin n → Fin m) P ρ :
    (atomicBody R names).realize (interpretation GorbowAtomicRegistry.ground P) ρ ↔
      (P ((instanceCodeTerm R names).realize (interpretation GorbowAtomicRegistry.ground P) ρ) ↔
        (substituteFormula (valueDictionary names) R).realize (interpretation GorbowAtomicRegistry.ground P) ρ) := by
  simp only [atomicBody,GorbowBooleanTruth.biconditional,Formula.realize,interpretation,GorbowRevisionSemantics.interpretation,iff_def]

private theorem atomicMinus {m : Nat} {R : Formula m} (hr : AtomicMinus R) :
    GorbowRevisionSemantics.MinusFormula R := by
  cases R <;> simp_all [AtomicMinus,GorbowRevisionSemantics.MinusFormula]

theorem atomicSchemas : Comparators.GorbowAtomicTruth.AtomicSchemas := by
  intro n m R names hr hn _ initial k
  apply (GorbowAtomicParametersProof.closureSemantics n (atomicBody R names) _).mpr
  intro ρ hρ
  have hex : ∀ j : Fin n, ∃ t : Term 0, ρ j=termCode t ∧ ArithmeticTerm t := by
    intro j
    exact (GorbowSortedBooleanCodeProof.exactDomains.2.2 (ρ j)).mp (hρ j)
  choose ts hcodes hts using hex
  apply (bodyRealization R names _ ρ).mpr
  rw [codeCalibration n m R names hn ts hts _ ρ hcodes]
  let σ := GorbowNameDictionary.dictionary names ts
  have hs := substituteFormula_realize R (stage GorbowAtomicRegistry.ground initial k) Fin.elim0 σ
  have hm := (GorbowRevisionSemanticsProof.fixedMinus GorbowAtomicRegistry.ground
      (extensions GorbowAtomicRegistry.ground initial k) (extensions GorbowAtomicRegistry.ground initial (k+1))).2
    m R (fun i => (σ i).realize (stage GorbowAtomicRegistry.ground initial k) Fin.elim0) (atomicMinus hr)
  have hv := (GorbowAtomicParametersProof.dictionaryCalibration n m names hn ts hts
    (extensions GorbowAtomicRegistry.ground initial (k+1)) ρ hcodes).2.1
  have he : (fun i => (σ i).realize (stage GorbowAtomicRegistry.ground initial k) Fin.elim0)=
      (fun i => (valueDictionary names i).realize (stage GorbowAtomicRegistry.ground initial (k+1)) ρ) := by
    funext i
    exact ((GorbowRevisionSemanticsProof.fixedMinus GorbowAtomicRegistry.ground
      (extensions GorbowAtomicRegistry.ground initial k) (extensions GorbowAtomicRegistry.ground initial (k+1))).1
      0 (σ i) Fin.elim0).trans (hv i).symm
  have hright := substituteFormula_realize R (stage GorbowAtomicRegistry.ground initial (k+1)) ρ (valueDictionary names)
  have hlast : R.realize (stage GorbowAtomicRegistry.ground initial (k+1))
      (fun i => (σ i).realize (stage GorbowAtomicRegistry.ground initial k) Fin.elim0) ↔
      (substituteFormula (valueDictionary names) R).realize (stage GorbowAtomicRegistry.ground initial (k+1)) ρ := by
    rw [he]
    exact hright.symm
  exact ((GorbowSortedRevisionProof.exactImage GorbowAtomicRegistry.ground
    (extensions GorbowAtomicRegistry.ground initial k)).1 (substituteFormula σ R)).trans
      (hs.trans (hm.trans hlast))

theorem otherCodedClauses : Comparators.GorbowAtomicTruth.OtherCodedClauses := by
  intro initial k
  have hb := GorbowRegistryDispatchProof.gorbowRegistryDispatch.2.1 GorbowAtomicRegistry.ground
    GorbowAtomicRegistryProof.originalDispatch.1 GorbowAtomicRegistryProof.originalDispatch.2 initial k
  have hq := GorbowRegistryDispatchProof.gorbowRegistryDispatch.2.2 GorbowAtomicRegistry.ground
    GorbowAtomicRegistryProof.originalDispatch.1 GorbowAtomicRegistryProof.originalDispatch.2 initial k
  exact ⟨hb.1,hb.2.1,hb.2.2.1,hb.2.2.2,hq⟩

theorem gorbowAtomicTruth : Comparators.GorbowAtomicTruth.Target :=
  ⟨codeCalibration,atomicSchemas,otherCodedClauses⟩
end LogicLineages.ComputabilityKnowledge.GorbowAtomicTruthProof
