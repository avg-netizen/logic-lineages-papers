module
public import LogicLineages.PermittedControl.ActualZeroClassConcreteAssemblyTargets
import LogicLineages.PermittedControl.ActualZeroClassConcreteAssemblyColumnProof
import LogicLineages.PermittedControl.ActualZeroClassConcreteAssemblyCohortProof
import LogicLineages.PermittedControl.ActualRankedZeroClassActualProof
import LogicLineages.PermittedControl.ActualCountOriginDispositionsProof
import LogicLineages.PermittedControl.ActualZeroClassOutsideRankedColumnsProof
import LogicLineages.PermittedControl.ActualZeroClassSelectedDispositionSumsProof
import LogicLineages.PermittedControl.ActualZeroClassSelectedDispositionAdmissibilityProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassConcreteAssembly
open scoped Classical
open OrdinalComparison FieldComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum ActualZeroClassReplacement
open ActualWeightedReadNormalization ActualRankedRowColumns ActualRankedZeroClass
open ActualZeroClassCohortTransfer ActualZeroClassRecombinedRow ActualCountOriginDispositions
open ActualZeroClassGroupedMovedCount ActualZeroClassSelectedCountKeys ActualZeroClassSelectedDispositionSums
open ActualZeroClassOutsideRankedColumns ActualZeroClassSelectedDispositionAdmissibility InnerTerminationTargets

private theorem replacementFromConcrete
    (f : Nat → Nat) (C r : Nat) (constant : Int) (raw xs : List Read)
    (annotations : List Annotation) (x₀ : Fin r) (q : NONote × NONote)
    (ledger : List DispositionEntry) (moved : List Read)
    (exactColumns : ConcreteEquations f C r constant raw xs annotations x₀ q ledger moved) :
    ZeroClassReplacement (rankedRow r constant raw)
      (concreteRow f C r constant xs annotations moved) := by
  let chosen := finiteClassColumns r (classReads f C xs annotations)
  exact ⟨chosen.1,chosen.2,x₀,q,dispositionAt (keyedLedger r ledger),exactColumns⟩

theorem exactConcreteZeroClassAssembly : ExactConcreteZeroClassAssembly := by
  intro f B hf ρ ordered C r constant raw xs annotations paid bounded normalized aligned ready actualC zero
  dsimp only
  intro tails
  let ps := cohort f C (xs.map Prod.fst) annotations
  let anchor := leastPrefix ps
  let outside := outsideCohort f C (xs.map Prod.fst) (xs.map Prod.snd) annotations
  let shift := (replaceRow f C (xs.map Prod.fst) (xs.map Prod.snd) annotations).2
  obtain ⟨valSupport,countSupport,classPresent,_,_,leading⟩ :=
    exactRankedClass f ρ r constant raw xs annotations C paid bounded normalized aligned actualC
  obtain ⟨x₀,q,hAnchor⟩ :=
    chooseFiniteAnchor f ρ C r raw xs annotations paid bounded normalized classPresent
  obtain ⟨moved,hm,hreads⟩ := chooseMovedReads f B hf ρ ordered C xs annotations aligned tails
  obtain ⟨ledger,hledger⟩ :=
    exactOriginDispositions f B hf ρ C xs annotations aligned ready anchor moved rfl hm hreads
  have hOutside := exactOutsideRankedColumns f ρ C r constant raw xs annotations
    paid bounded normalized aligned actualC
  have hSums := exactSelectedDispositionSums f ρ C r constant raw xs annotations anchor
    x₀ q ledger moved paid bounded normalized aligned actualC hAnchor hledger
  have hRanks := exactSelectedDispositionAdmissibility f ρ C r constant raw xs annotations
    anchor x₀ q ledger moved paid bounded normalized aligned actualC hAnchor hledger
  have hEmptyValue := movedValueColumnZero f ρ r anchor ps moved hm
  have hAppend := appendRankedColumns r (constant + shift) outside moved
  have equations : ConcreteEquations f C r constant raw xs annotations x₀ q ledger moved := by
    refine ⟨valSupport,countSupport,classPresent,leading.symm.trans zero,hRanks,?_,?_,?_⟩
    · unfold concreteRow
      rw [hAppend.1,hOutside.1,hEmptyValue,add_zero]
    · unfold concreteRow
      rw [hAppend.2,hOutside.2,hSums.1]
    · change constant + (replaceRow f C (xs.map Prod.fst) (xs.map Prod.snd) annotations).2 =
        constant + _
      rw [hSums.2]
  exact ⟨moved,ledger,x₀,q,hm,hreads,hAnchor,hledger,equations,
    replacementFromConcrete f C r constant raw xs annotations x₀ q ledger moved equations⟩

end LogicLineages.PermittedControl.ActualZeroClassConcreteAssembly
