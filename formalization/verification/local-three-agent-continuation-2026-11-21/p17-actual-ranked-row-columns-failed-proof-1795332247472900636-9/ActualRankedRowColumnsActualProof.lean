module
public import LogicLineages.PermittedControl.ActualRankedRowColumnsTargets
import LogicLineages.PermittedControl.ActualRankedRowColumnsWeightsProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRankedRowColumns
open OrdinalComparison FieldComparison PreparedProjection
open ActualZeroClassReplacement ActualWeightedReadNormalization
open SelectedNonlinearImageBounds (NonlinearField)

private theorem memberRead (f : Nat → Nat) (ρ : Nat → Nat) (xs : List Read)
    (reads : liftedReads f ρ xs) (read : Read) (member : read ∈ xs) :
    LowerOperandActual f ρ read.1.2 read.2 ∧
      lowerOperandRead f ρ read.1.2 = some (some read.2) := by
  induction xs with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons a xs next =>
      rcases List.mem_cons.mp member with same | tail
      · subst read
        exact ⟨reads.1,reads.2.1⟩
      · exact next reads.2.2 tail

theorem exactRankedReads : ExactRankedReads := by
  intro f ρ r c xs paid bounded
  let row := rankedRow r c xs
  obtain ⟨_,countWeight,valueWeight,_,countSupport,valueSupport⟩ :=
    exactRankedCoefficients r c xs
  obtain ⟨out,normalized,keys,_,outputReads,sameValue,records⟩ :=
    (StatementChecks.fixed_actualWeightedNormalizedReads f ρ xs).2 paid
  have witness (op : LowerOperand) (active : op ∈ (groupedWeights xs).support) :
      WitnessesColumn f ρ out op (groupedWeights xs op) := by
    have member : op ∈ out.map (fun rd => rd.1.2) := by
      rw [keys]
      exact Finset.mem_toList.mpr active
    obtain ⟨rd,retained,key⟩ := List.mem_map.mp member
    have weight : rd.1.1 = groupedWeights xs op := by
      simpa only [key] using (records rd retained).1
    have identical : rd = (((groupedWeights xs op,op),rd.2) : Read) :=
      Prod.ext (Prod.ext weight key) rfl
    obtain ⟨actual,reader⟩ := memberRead f ρ out outputReads rd retained
    refine ⟨rd.2,?_,?_,?_⟩
    · rw [← identical]
      exact retained
    · rw [← key]
      exact actual
    · rw [← key]
      exact reader
  refine ⟨out,normalized,outputReads,sameValue,?_,?_,?_⟩
  · intro k member
    rw [countWeight k]
    exact witness (countOperand r k) ((countSupport k).mp member)
  · intro k member
    have active := (valueSupport k).mp member
    rw [valueWeight k active.1]
    exact witness (valueOperand r k) active.2
  · intro rd retained
    obtain ⟨weight,nonzero,prior,priorMem,sameOp,_⟩ := records rd retained
    have rankBound : rd.1.2.rank < r := by
      simpa only [sameOp] using bounded prior priorMem
    have inSupport : rd.1.2 ∈ (groupedWeights xs).support :=
      Finsupp.mem_support_iff.mpr (fun zero => nonzero (weight.trans zero))
    cases shape : rd.1.2 with
    | coordinate n => exact (by simp only [IsInRankedColumn,shape] : IsInRankedColumn row rd)
    | ordinary n F =>
        simp only [IsInRankedColumn,shape]
        intro active
        rw [shape] at rankBound
        let i : Fin r := ⟨n,rankBound⟩
        have literal : valueOperand r (i,F) = rd.1.2 := shape.symm
        have listed : valueOperand r (i,F) ∈ (groupedWeights xs).support := by
          rw [literal]
          exact inSupport
        refine ⟨i,rfl,(valueSupport (i,F)).mpr ⟨active,listed⟩,?_⟩
        rw [valueWeight (i,F) active,literal,← weight]
    | count n lam mu =>
        simp only [IsInRankedColumn,shape]
        rw [shape] at rankBound
        let i : Fin r := ⟨n,rankBound⟩
        have literal : countOperand r ((lam,mu),i) = rd.1.2 := shape.symm
        have listed : countOperand r ((lam,mu),i) ∈ (groupedWeights xs).support := by
          rw [literal]
          exact inSupport
        refine ⟨i,rfl,(countSupport ((lam,mu),i)).mpr listed,?_⟩
        rw [countWeight ((lam,mu),i),literal,← weight]

end LogicLineages.PermittedControl.ActualRankedRowColumns
