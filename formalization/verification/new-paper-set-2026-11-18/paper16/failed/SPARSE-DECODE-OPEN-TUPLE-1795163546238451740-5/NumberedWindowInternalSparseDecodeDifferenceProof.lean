module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeDifferenceProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn suc eqnRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm trans)
open ID1Completion.InternalAdditionLawsProof (add congAddLeft)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF addRelabel)
open ID1Completion.InternalUnpairReverseSyntaxProof (weakOrderCases)
open ID1Completion.InternalEqualityTestSubtractionSupportProof (subGraph subGraphRename subTransport)
open ID1Completion.InternalEqualityTestSubtractionProof (diagonal)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalEqualityTest (subtract)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Recover the actual additive equation from truncated subtraction only
where a retained object arithmetic derivation proves the nontruncation bound. -/
theorem differenceEquation (lo hi r : OTerm α)
    (hb : Nonempty (Derivation body Γ (ltF lo (suc hi))))
    (hs : Nonempty (Derivation body Γ (subGraph r lo hi))) :
    Nonempty (Derivation body Γ (eqn (add lo r) hi)) := by
  apply weakOrderCases Γ lo hi _ hb
  intro β j Δ w hJ ⟨e⟩
  rw [eqnRelabel,addRelabel]
  let l := lo.relabel j
  let h := hi.relabel j
  let v := r.relabel j
  have supplied := renameInto hs j Δ hJ
  rw [subGraphRename] at supplied
  have atWitness := subTransport w l (add l w) l h ⟨refl l⟩ ⟨e⟩ (diagonal l w)
  obtain ⟨same⟩ := valueUnique subtract v w (Fin.cons l (Fin.cons h Fin.elim0)) supplied atWitness
  exact ⟨trans (congAddLeft l same) e⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeDifferenceProof
