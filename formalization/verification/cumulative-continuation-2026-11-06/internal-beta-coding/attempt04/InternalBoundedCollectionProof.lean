module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCollectionSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCollectionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalCoprimeMultiple InternalCoprimeMultipleSyntaxProof InternalCoprimeMultipleBoundedProof
open InternalRelationalCRT InternalRelationalCRTSyntaxProof InternalRelationalCRTChoiceProof
open InternalRelationalCRTSupportProof InternalBoundedCollection InternalBoundedCollectionSyntaxProof
open InternalBoundedCollectionSupportProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionSyntaxProof
open InternalPositiveUnfoldingSupportProof InternalLeastNumberSyntaxProof InternalOriginalOrderSyntaxProof
open InternalOriginalOrderProof InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof InternalDerivationRenamingSyntaxProof InternalQuotientComparisonSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
/-- The step chooses the last witness and enlarges the old bound by addition. -/
theorem collectionStep (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (n : OTerm α)
    (hc : Nonempty (Derivation body Gamma (collection R n)))
    (ha : Nonempty (Derivation body Gamma (availableBelow R (suc n)))) :
    Nonempty (Derivation body Gamma (collection R (suc n))) := by
  have hl := availableLast R n ha
  apply collectionCases Gamma R n (collection R (suc n)) hc
  intro β j Delta K hj hb
  have hl' := renameInto hl j Delta hj
  rw [existsRename,atIndexRename] at hl'
  rw [collectionRename,sucRelabel]
  let Q := R.relabel (Sum.map (Sum.map j id) id)
  let N := n.relabel j
  apply existsCases Delta (atIndex Q N) (collection Q (suc N)) hl'
  intro γ l Theta r hl hr
  rw [atIndexRename] at hr
  rw [collectionRename,sucRelabel]
  have hb' := renameInto hb l Theta hl
  rw [boundBelowRename] at hb'
  let S := Q.relabel (Sum.map (Sum.map l id) id)
  let M := N.relabel l
  let L := K.relabel l
  let H := suc (add L r)
  apply collectionIntroduction S H (suc M)
  have hold := boundBelowMono S L H M hb' (leftLtSuccAdd L r)
  have hnew := witnessIntroduction (atIndex S M) H r hr (rightLtSuccAdd L r)
  apply boundedStep (witness S (H.relabel Sum.inl)) M hold
  rw [boundBelowAt]
  exact hnew

/-- Actual PA induction on the object index bound, not meta-level finite choice. -/
theorem actualBoundedCollection : InternalBoundedCollectionTargets.ActualBoundedCollection := by
  intro body α n R
  let Q := R.relabel (Sum.map (Sum.map (Sum.inl : α → α ⊕ Fin 1) id) id)
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let theta := (availableBelow Q x).imp (collection Q x)
  have hb : Nonempty (Derivation body [] (instantiate theta (emb z))) := by
    simp only [theta,Q,x,impInstantiate,availableBelowInstantiate,collectionInstantiate]
    obtain ⟨h⟩ := collectionIntroduction (body := body) (Gamma := [availableBelow R z]) R z z
      (boundedZero _)
    exact ⟨Derivation.implicationIntroduction h⟩
  have hs : Nonempty (Derivation body [theta] (successorInstance theta)) := by
    have hnext : successorInstance theta = (availableBelow Q (suc x)).imp (collection Q (suc x)) := by
      simp only [theta,Q,x,successorInstance,nextEmbedding,impSubst,
        availableBelowSubst,collectionSubst,relationLiftNext,varNext]
    rw [hnext]
    let p := availableBelow Q (suc x)
    have hi : Derivation body (p :: [theta]) theta := Derivation.hypothesis (by simp)
    have hp : Derivation body (p :: [theta]) p := Derivation.hypothesis List.mem_cons_self
    obtain ⟨hr⟩ := boundedRestrict (existsOne Q) x ⟨hp⟩
    have hc := Derivation.implicationElimination hi hr
    obtain ⟨h⟩ := collectionStep Q x ⟨hc⟩ ⟨hp⟩
    exact ⟨Derivation.implicationIntroduction h⟩
  obtain ⟨hb⟩ := hb
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb n) (natInduction theta hb hs)
  simpa only [theta,Q,x,impInstantiate,availableBelowInstantiate,collectionInstantiate] using
    (show Nonempty (Derivation body [] _) from ⟨h⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCollectionProof
