module

public import LogicLineages.ComputabilityKnowledge.OracleRelativeRecursionTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleRelativeRecursionProof
open OracleRelativeRecursion OracleRelativeRecursionTargets

theorem relativeComposition : RelativeComposition := by
  intro O f g hf hg
  apply RecursiveIn.iff_nat.mpr
  exact ((RecursiveIn.iff_nat.mp hf).comp (RecursiveIn.iff_nat.mp hg)).of_eq (fun _ => by simp)

theorem relativeNumericPairing : RelativeNumericPairing := by
  intro O f g hf hg
  apply RecursiveIn.iff_nat.mpr
  exact ((RecursiveIn.iff_nat.mp hf).pair (RecursiveIn.iff_nat.mp hg)).of_eq (fun _ => by simp [Seq.seq])

theorem relativePrimitiveRecursion : RelativePrimitiveRecursion := by
  intro O f g hf hg
  apply RecursiveIn.iff_nat.mpr
  apply ((RecursiveIn.iff_nat.mp hf).prec (RecursiveIn.iff_nat.mp hg)).of_eq
  intro z
  dsimp only [parameterRec]
  generalize z.unpair = p
  rcases p with ⟨a, n⟩
  induction n with
  | zero => rfl
  | succ n ih =>
      dsimp only at ih
      simp only [Bind.bind] at ih ⊢
      simp only [Nat.rec_add_one, ih, Part.bind_some]

theorem relativePartialSearch : RelativePartialSearch := by
  intro O test ht
  apply RecursiveIn.iff_nat.mpr
  exact (RecursiveIn.iff_nat.mp ht).rfind.of_eq (fun _ => by simp [zeroSearch])

end LogicLineages.ComputabilityKnowledge.OracleRelativeRecursionProof
