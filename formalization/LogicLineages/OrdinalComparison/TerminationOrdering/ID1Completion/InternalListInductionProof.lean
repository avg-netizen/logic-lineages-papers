module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalListCodec InternalListInduction InternalListInductionSyntaxProof
open InternalListCodecSupportProof InternalListCodecDecompositionSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalRecursionClosureLogicProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalControlGraphChoiceProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalSourceInversionSupportProof InternalPositiveUnfoldingSupportProof
open InternalOriginalOrderSyntaxProof InternalBetaTotalityProof
open SourceComputabilityFormulaSupportProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Obtain both destructor witnesses internally, reconstruct the original
constructor, and invoke the invariant only at the strictly smaller tail. -/
theorem nonzeroAt (theta : Formula (α ⊕ Fin 1)) (n : OTerm α)
    (hp : Nonempty (Derivation body Gamma (premises theta)))
    (hb : Nonempty (Derivation body Gamma (InternalStrongInduction.below theta n)))
    (hn : Nonempty (Derivation body Gamma (eqn n z).not)) :
    Nonempty (Derivation body Gamma (atCode theta n)) := by
  apply programCases headCode (Fin.cons n Fin.elim0) _
  intro β j Delta h hj hh
  rw [atCodeRename]
  simp only [consTermRename, emptyRename] at hh
  have hp' := renameInto hp j Delta hj
  rw [premisesRename] at hp'
  have hb' := renameInto hb j Delta hj
  rw [InternalStrongInductionSyntaxProof.belowRename] at hb'
  have hn' := renameInto hn j Delta hj
  rw [nonzeroRename] at hn'
  apply programCases tailCode (Fin.cons (n.relabel j) Fin.elim0) _
  intro γ k E t hk ht
  rw [atCodeRename]
  simp only [consTermRename, emptyRename] at ht
  have hp'' := renameInto hp' k E hk
  rw [premisesRename] at hp''
  have hb'' := renameInto hb' k E hk
  rw [InternalStrongInductionSyntaxProof.belowRename] at hb''
  have hn'' := renameInto hn' k E hk
  rw [nonzeroRename] at hn''
  have hh' := renameInto hh k E hk
  rw [unaryGraphRename] at hh'
  have hc := reconstructNonzero ((n.relabel j).relabel k) (h.relabel k) t hn'' hh' ht
  obtain ⟨hlt⟩ := consTailDescent ((n.relabel j).relabel k) (h.relabel k) t hc
  obtain ⟨hb''⟩ := hb''
  have hi := Derivation.universalElimination (emb t) hb''
  rw [InternalStrongInductionSyntaxProof.belowElimSyntax] at hi
  obtain ⟨hp''⟩ := hp''
  exact constructorApply _ ((n.relabel j).relabel k) (h.relabel k) t
    ⟨Derivation.conjunctionRight hp''⟩ hc
    ⟨Derivation.implicationElimination hi hlt⟩

/-- The zero/nonzero split is performed by an object-calculus proof of
excluded middle. The input code is an arbitrary arithmetic term. -/
theorem stepAt (theta : Formula (α ⊕ Fin 1)) (n : OTerm α)
    (hp : Nonempty (Derivation body Gamma (premises theta)))
    (hb : Nonempty (Derivation body Gamma (InternalStrongInduction.below theta n))) :
    Nonempty (Derivation body Gamma (atCode theta n)) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hb⟩ := hb
  have hz : Derivation body (eqn n z :: Gamma) (atCode theta n) := by
    have he : Derivation body (eqn n z :: Gamma) (eqn n z) :=
      Derivation.hypothesis List.mem_cons_self
    exact Derivation.equalityElimination theta (emb z) (emb n) (symm he)
      (Derivation.conjunctionLeft (addHyp hp _))
  obtain ⟨hs⟩ := nonzeroAt theta n
    ⟨addHyp hp (eqn n z).not⟩ ⟨addHyp hb (eqn n z).not⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination (excludedMiddle (eqn n z))
    (Derivation.implicationIntroduction hz) (Derivation.implicationIntroduction hs)⟩

theorem actualOriginalListInduction : InternalListInductionTargets.ActualOriginalListInduction := by
  intro body α theta
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let Delta := InternalStrongInduction.below (InternalStrongInduction.lift theta) x ::
    ([premises theta] : List (Formula α)).map weaken
  have hp : Nonempty (Derivation body Delta
      (premises (InternalStrongInduction.lift theta))) := by
    have h : Derivation body Delta (weaken (premises theta)) :=
      Derivation.hypothesis (by simp [Delta])
    simpa only [weaken, premisesRename, InternalStrongInduction.lift] using
      (show Nonempty (Derivation body Delta (weaken (premises theta))) from ⟨h⟩)
  have hb : Nonempty (Derivation body Delta
      (InternalStrongInduction.below (InternalStrongInduction.lift theta) x)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hs := stepAt (InternalStrongInduction.lift theta) x hp hb
  change Nonempty (Derivation body Delta
    (instantiate (InternalStrongInduction.lift theta) (emb (.var (.inr 0))))) at hs
  rw [InternalStrongInductionSyntaxProof.freshLift] at hs
  obtain ⟨d⟩ := InternalStrongInductionProof.strongInduction
    (Gamma := [premises theta]) theta hs
  exact ⟨Derivation.implicationIntroduction d⟩

theorem actualOriginalListInductionAtCode :
    InternalListInductionTargets.ActualOriginalListInductionAtCode := by
  intro body α Gamma theta n hp
  obtain ⟨h⟩ := closedApply (actualOriginalListInduction body α theta) hp
  exact ⟨Derivation.universalElimination (emb n) h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
