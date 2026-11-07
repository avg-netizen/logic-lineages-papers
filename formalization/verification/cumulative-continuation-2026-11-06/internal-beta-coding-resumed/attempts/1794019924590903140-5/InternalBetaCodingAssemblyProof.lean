module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCodingSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCollectionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalResidueBoundProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaModulusCoprimalityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaModulusCoprimalityExistenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCongruenceProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCodingAssemblyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open InternalPositiveUnfoldingSupportProof InternalAdditionLawsProof
open InternalCoprimeMultiple InternalCoprimeMultipleSyntaxProof InternalCoprimeMultipleBoundedProof
open InternalRelationalCRT InternalRelationalCRTSyntaxProof InternalRelationalCRTChoiceProof
open InternalBoundedCollection InternalBoundedCollectionSyntaxProof
open InternalBetaCoding InternalBetaCodingSyntaxProof
open InternalBetaWitness InternalBetaDivisionProof InternalBetaDivisionSyntaxProof
open InternalModularArithmeticProof InternalBezoutExistenceConsumerProof
open InternalResidueBoundTargets InternalResidueBoundProof
open InternalBetaModulusCoprimality InternalBetaModulusCoprimalityProof
open InternalBetaModulusCoprimalityExistenceProof InternalBetaCongruenceProof

theorem scalePredRename {α β : Type} (b K : OrdinaryArithmetic.Term α) (j : α → β) :
    (scalePred b K).relabel j = scalePred (b.relabel j) (K.relabel j) := by
  simp only [scalePred, addRelabel, mulRelabel, sucRelabel]

theorem betaFamilyRename {α β : Type} (b : OrdinaryArithmetic.Term α) (j : α → β) :
    (betaFamily b).relabel (Sum.map j id) = betaFamily (b.relabel j) := by
  simp only [betaFamily, mulRelabel, sucRelabel, Term.relabel_relabel, mapInl, varMap]

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Preserve the actual relation witness while converting its bounded congruence
to the unchanged original beta formula. -/
theorem chosenToBeta (R : Formula (α ⊕ Fin 1)) (a b K i : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma
      (chosen (R ⊓ ltF (.var (.inr 0)) (K.relabel Sum.inl))
        (modulus (suc (scalePred b K)) i) a))) :
    Nonempty (Derivation body Gamma (existsOne
      (R ⊓ betaF (a.relabel Sum.inl) ((suc (scalePred b K)).relabel Sum.inl)
        (i.relabel Sum.inl) (.var (.inr 0))))) := by
  obtain ⟨h⟩ := h
  let B := suc (scalePred b K)
  let r : OrdinaryArithmetic.Term (α ⊕ Fin 1) := .var (.inr 0)
  let mat : Formula (α ⊕ Fin 1) :=
    (R ⊓ ltF r (K.relabel Sum.inl)) ⊓
      cf (a.relabel Sum.inl) r ((modulus B i).relabel Sum.inl)
  let Delta := mat :: Gamma.map weaken
  have hm : Derivation body Delta mat := Derivation.hypothesis List.mem_cons_self
  have hr : Nonempty (Derivation body Delta (ltF r (K.relabel Sum.inl))) :=
    ⟨Derivation.conjunctionRight (Derivation.conjunctionLeft hm)⟩
  have hc : Nonempty (Derivation body Delta
      (cf (a.relabel Sum.inl) r (modulus (B.relabel Sum.inl) (i.relabel Sum.inl)))) := by
    simpa only [modulusRename] using
      (show Nonempty (Derivation body Delta
        (cf (a.relabel Sum.inl) r ((modulus B i).relabel Sum.inl))) from
        ⟨Derivation.conjunctionRight hm⟩)
  have hb : Nonempty (Derivation body Delta
      (ltF r (modulus (B.relabel Sum.inl) (i.relabel Sum.inl)))) := by
    simpa only [B, sucRelabel, scalePredRename] using
      (actualResidueBound body (α ⊕ Fin 1) Delta (b.relabel Sum.inl)
        (K.relabel Sum.inl) (i.relabel Sum.inl) r hr)
  obtain ⟨hbeta⟩ := boundedCongruenceBeta (a.relabel Sum.inl) (B.relabel Sum.inl)
    (i.relabel Sum.inl) r hc hb
  exact ⟨existsMap h (Derivation.conjunctionIntroduction
    (Derivation.conjunctionLeft (Derivation.conjunctionLeft hm)) hbeta)⟩

/-- The bounded universal is retained literally; every original relation witness
keeps its strict bound until the original beta bridge has been applied. -/
theorem residuesToCoded (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (a b K n : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma
      (residuesBelow (betaFamily (suc (scalePred b K))) (boundedRelation R K) a n))) :
    Nonempty (Derivation body Gamma (codedBelow R a (suc (scalePred b K)) n)) := by
  let B := suc (scalePred b K)
  let x : OrdinaryArithmetic.Term (α ⊕ Fin 1) := .var (.inr 0)
  let p : Formula (α ⊕ Fin 1) :=
    chosen (boundedRelation R K) (suc (betaFamily B)) (a.relabel Sum.inl)
  let q : Formula (α ⊕ Fin 1) := existsOne
    (R ⊓ betaF ((a.relabel Sum.inl).relabel Sum.inl)
      ((B.relabel Sum.inl).relabel Sum.inl) (x.relabel Sum.inl) (.var (.inr 0)))
  have hp : Nonempty (Derivation body Gamma (bounded p n)) := h
  have hmap : Nonempty (Derivation body Gamma (allOne (p.imp q))) := by
    apply Nonempty.intro
    apply Derivation.universalIntroduction
    apply Derivation.implicationIntroduction
    have hchosen : Nonempty (Derivation body (p :: Gamma.map weaken) p) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hc : Nonempty (Derivation body (p :: Gamma.map weaken)
        (chosen (R ⊓ ltF (.var (.inr 0)) ((K.relabel Sum.inl).relabel Sum.inl))
          (modulus (suc (scalePred (b.relabel Sum.inl) (K.relabel Sum.inl))) x)
          (a.relabel Sum.inl))) := by
      simpa only [p, boundedRelation, betaFamily, modulus, B, x,
        sucRelabel, scalePredRename] using hchosen
    obtain ⟨hbeta⟩ := chosenToBeta R (a.relabel Sum.inl) (b.relabel Sum.inl)
      (K.relabel Sum.inl) x hc
    simpa only [q, B, sucRelabel, scalePredRename] using hbeta
  exact boundedMap p q n hp hmap

/-- A supplied internal witness bound and suitable internal difference multiple
are enough for the actual shared code, by the proved relational CRT. -/
theorem codingOfSuitableBounds (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (b K n : OrdinaryArithmetic.Term α)
    (hm : Nonempty (Derivation body Gamma (differenceMultiples (suc b) n)))
    (hb : Nonempty (Derivation body Gamma (boundBelow R K n))) :
    Nonempty (Derivation body Gamma (coding R n)) := by
  let B := suc (scalePred b K)
  obtain ⟨hd⟩ := actualScaleMultiples body α Gamma b K n hm
  obtain ⟨hp⟩ := actualBetaModulusPairwise body α (scalePred b K) n
  have hp := Derivation.implicationElimination (weakenClosed hp Gamma) hd
  obtain ⟨hb⟩ := hb
  obtain ⟨hcrt⟩ := InternalRelationalCRTProof.actualRelationalCRT body α n
    (betaFamily B) (boundedRelation R K)
  have hs : Nonempty (Derivation body Gamma
      (solution (betaFamily B) (boundedRelation R K) n)) :=
    ⟨Derivation.implicationElimination (weakenClosed hcrt Gamma)
      (Derivation.conjunctionIntroduction hp hb)⟩
  apply solutionCases Gamma (betaFamily B) (boundedRelation R K) n (coding R n) hs
  intro β j Delta a _ hr
  rw [codingRename]
  have hr' : Nonempty (Derivation body Delta
      (residuesBelow (betaFamily (suc (scalePred (b.relabel j) (K.relabel j))))
        (boundedRelation (R.relabel (Sum.map (Sum.map j id) id)) (K.relabel j))
        a (n.relabel j))) := by
    simpa only [betaFamilyRename, boundedRelationRename, B, sucRelabel, scalePredRename] using hr
  exact codingIntroduction (R.relabel (Sum.map (Sum.map j id) id)) a
    (suc (scalePred (b.relabel j) (K.relabel j))) (n.relabel j)
    (residuesToCoded _ a (b.relabel j) (K.relabel j) (n.relabel j) hr')

/-- Genuine fresh-witness elimination for the already proved positive common
multiple existence formula. -/
theorem positiveMultipleCases (Gamma : List (Formula α)) (n : OrdinaryArithmetic.Term α)
    (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (positiveMultipleExists n)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (b : OrdinaryArithmetic.Term β),
      (∀ f ∈ Gamma, f.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (differenceMultiples (suc b) (n.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  obtain ⟨hk⟩ := k (α ⊕ Fin 1) Sum.inl _ (.var (.inr 0))
    (by intro f hf; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f, hf, rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination h hk⟩

/-- The difference multiple is obtained internally, not supplied as a premise
of the eventual coding theorem. -/
theorem codingOfBound (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (K n : OrdinaryArithmetic.Term α)
    (hb : Nonempty (Derivation body Gamma (boundBelow R K n))) :
    Nonempty (Derivation body Gamma (coding R n)) := by
  obtain ⟨hm⟩ := actualPositiveMultipleExists body α n
  apply positiveMultipleCases Gamma n (coding R n) ⟨weakenClosed hm Gamma⟩
  intro β j Delta b hi hd
  have hb' := renameInto hb j Delta hi
  rw [boundBelowRename] at hb'
  rw [codingRename]
  exact codingOfSuitableBounds (R.relabel (Sum.map (Sum.map j id) id)) b
    (K.relabel j) (n.relabel j) hd hb'

/-- The bound itself is also eliminated internally, leaving precisely the
original coding formula with its original free parameters. -/
theorem codingOfCollection (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (n : OrdinaryArithmetic.Term α)
    (hc : Nonempty (Derivation body Gamma (collection R n))) :
    Nonempty (Derivation body Gamma (coding R n)) := by
  apply collectionCases Gamma R n (coding R n) hc
  intro β j Delta K _ hb
  rw [codingRename]
  exact codingOfBound (R.relabel (Sum.map (Sum.map j id) id)) K (n.relabel j) hb
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCodingAssemblyProof
