module
public import LogicLineages.CartierObserverCurrent.FullHigherPolesTargets
public import LogicLineages.CartierObserverCurrent.FullTransientProof
public import LogicLineages.CartierObserverCurrent.PeriodLaurentGenericProof
public meta import LogicLineages.Audit
@[expose] public section
universe u v
namespace LogicLineages.CartierObserverCurrent.FullHigherPoles

theorem repeatedWord : Targets.RepeatedWord.{u} := by
  intro K _ _ _ f j
  induction j generalizing f with
  | zero => rfl
  | succ j ih =>
    simp only [List.replicate_succ, MixedWord.execute, MixedProper.step, if_true]
    rw [ih, Function.iterate_succ_apply]

theorem removalAndResidues : Targets.RemovalAndResidues.{u,v} := by
  intro K L _ _ _ _ _ _ σ d hd P hP
  let f : RatFunc K := algebraMap (Polynomial K) (RatFunc K) P /
    algebraMap (Polynomial K) (RatFunc K) (SourceBudget.denominator K d)
  let state : Nat → RatFunc L := fun j => Naturality.rationalMap σ
    ((Basic.actualDifferentialCartier (K := K))^[j] f)
  let a := SourceBudget.transient d
  change (∀ j, MixedProper.proper (state j)) ∧
    (∀ j z, PoleContraction.poleOrder z (state (a + j)) ≤ 1) ∧
    (∀ z j, (LogicLineages.OrdinalComparison.actualTranslatedRationalEmbedding z
      (state (a + j))).coeff (-1) = (iterateFrobeniusEquiv L 2 j).symm
        ((LogicLineages.OrdinalComparison.actualTranslatedRationalEmbedding z (state a)).coeff (-1)))
  have transient (j : Nat) :=
    FullTransient.binaryTransient.2.2.2 K L σ d hd P hP (List.replicate j true)
  have natural (j : Nat) (g : RatFunc K) :
      Naturality.rationalMap σ ((Basic.actualDifferentialCartier (K := K))^[j] g) =
        (Basic.actualDifferentialCartier (K := L))^[j] (Naturality.rationalMap σ g) := by
    simpa only [repeatedWord] using
      Naturality.extensionWord K L σ (List.replicate j true) g
  refine ⟨?_, ?_, ?_⟩
  · intro j
    simpa only [repeatedWord] using (transient j).1
  · intro j z
    have hlen : SourceBudget.transient d ≤ (List.replicate (a + j) true).length := by
      simp only [List.length_replicate]
      exact Nat.le_add_right a j
    simpa only [repeatedWord] using (transient (a + j)).2.2 hlen z
  · intro z j
    have heq : state (a + j) =
        (LogicLineages.OrdinalComparison.actualDifferentialCartier (K := L))^[j] (state a) := by
      change Naturality.rationalMap σ ((Basic.actualDifferentialCartier (K := K))^[a + j] f) = _
      rw [Nat.add_comm a j, Function.iterate_add_apply, natural]
      rfl
    rw [heq]
    exact PeriodLaurentGeneric.iteratedResidue L z (state a) j

theorem completeHigherPoles : Targets.CompleteHigherPoles.{u,v} :=
  ⟨repeatedWord, PeriodLaurentGeneric.cartierIdentity, Naturality.extensionWord,
    removalAndResidues⟩

#audit_namespace LogicLineages.CartierObserverCurrent.FullHigherPoles
end LogicLineages.CartierObserverCurrent.FullHigherPoles
