module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCongruenceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalModularArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaUniquenessProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCongruenceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalBetaWitness InternalBetaWitnessProof InternalBetaDivisionProof InternalBetaDivisionSyntaxProof
open InternalBetaTotalityProof InternalBetaTotalitySyntaxProof InternalBetaUniquenessProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalAdditionLawsProof
open InternalMultiplicationLawsProof InternalPositiveUnfoldingSupportProof
open InternalModularArithmeticProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem betaCongruence (c b i r : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (betaF c b i r))) :
    Nonempty (Derivation body Gamma (cf c r (modulus b i))) := by
  apply betaCases Gamma c b i r _ h
  intro β j Delta q d _ he
  rw [congruentRename,modulusRename]
  rw [InternalBetaDivisionProof.equationEmbedding] at he
  obtain ⟨he⟩ := he
  apply InternalModularArithmeticProof.actualIntroduction body β Delta _ _ _ z q
  rw [InternalModularArithmeticProof.equationEmbedding]
  exact ⟨trans (trans (congAddLeft _ (multiplicationLeftZero _)) (addZero _))
    (trans (Derivation.conjunctionLeft he) (commutativity _ _))⟩

theorem boundedCongruenceEquality (r s m : OrdinaryArithmetic.Term α)
    (hc : Nonempty (Derivation body Gamma (cf r s m)))
    (hr : Nonempty (Derivation body Gamma (ltF r m)))
    (hs : Nonempty (Derivation body Gamma (ltF s m))) :
    Nonempty (Derivation body Gamma (eqn r s)) := by
  apply orderCases Gamma r m _ hr
  intro β j Delta d hi hd
  rw [eqnRelabel]
  have hc' := renameInto hc j Delta hi
  have hs' := renameInto hs j Delta hi
  rw [congruentRename] at hc'
  rw [orderRename] at hs'
  apply orderCases Delta (s.relabel j) (m.relabel j) _ hs'
  intro γ k Theta e hk he
  rw [eqnRelabel]
  have hc'' := renameInto hc' k Theta hk
  rw [congruentRename] at hc''
  have hd' := renameInto hd k Theta hk
  simp only [eqnRelabel,addRelabel,sucRelabel] at hd'
  apply congruenceCases Theta ((r.relabel j).relabel k) ((s.relabel j).relabel k)
    ((m.relabel j).relabel k) _ hc''
  intro δ l Xi q p hl hh
  rw [eqnRelabel]
  have hd'' := renameInto hd' l Xi hl
  have he' := renameInto he l Xi hl
  simp only [eqnRelabel,addRelabel,sucRelabel] at hd'' he'
  rw [InternalModularArithmeticProof.equationEmbedding] at hh
  obtain ⟨hd''⟩ := hd''
  obtain ⟨he'⟩ := he'
  obtain ⟨hh⟩ := hh
  let R := ((r.relabel j).relabel k).relabel l
  let S := ((s.relabel j).relabel k).relabel l
  let M := ((m.relabel j).relabel k).relabel l
  exact remainderUnique Xi (add R (mul q M)) M q p R S ((d.relabel k).relabel l) (e.relabel l)
    (commutativity R (mul q M)) (trans hh (commutativity S (mul p M))) hd'' he'

def betaResidueTransport (c b i r s : OrdinaryArithmetic.Term α)
    (he : Derivation body Gamma (eqn r s)) (hb : Derivation body Gamma (betaF c b i r)) :
    Derivation body Gamma (betaF c b i s) := by
  let theta := betaF (c.relabel Sum.inl) (b.relabel Sum.inl) (i.relabel Sum.inl) (.var (.inr 0))
  have h := Derivation.equalityElimination theta (emb r) (emb s) he
  simp only [theta,betaF,betaInstantiate,liftBind,varBind] at h
  exact h hb

theorem boundedCongruenceBeta (c b i r : OrdinaryArithmetic.Term α)
    (hc : Nonempty (Derivation body Gamma (cf c r (modulus b i))))
    (hr : Nonempty (Derivation body Gamma (ltF r (modulus b i)))) :
    Nonempty (Derivation body Gamma (betaF c b i r)) := by
  obtain ⟨ht⟩ := actualBetaTotality body α c b i
  apply remainderCases Gamma c b i _ ⟨weakenClosed ht Gamma⟩
  intro β j Delta s hi hb
  rw [betaRename]
  have hc' := renameInto hc j Delta hi
  have hr' := renameInto hr j Delta hi
  rw [congruentRename,modulusRename] at hc'
  rw [orderRename,modulusRename] at hr'
  have hcs := betaCongruence _ _ _ _ hb
  have hsc := InternalModularArithmeticProof.actualSymmetry body β Delta _ _ _ hcs
  have hsr := InternalModularArithmeticProof.actualTransitivity body β Delta _ _ _ _ hsc hc'
  obtain ⟨bd⟩ := actualBetaRemainderBound body β (c.relabel j) (b.relabel j) (i.relabel j) s
  obtain ⟨hb⟩ := hb
  have hs := Derivation.implicationElimination (weakenClosed bd Delta) hb
  obtain ⟨he⟩ := boundedCongruenceEquality s (r.relabel j) (modulus (b.relabel j) (i.relabel j)) hsr ⟨hs⟩ hr'
  exact ⟨betaResidueTransport _ _ _ _ _ he hb⟩

theorem actualBetaCongruence : InternalBetaCongruenceTargets.ActualBetaCongruence := by
  intro body α c b i r
  obtain ⟨h⟩ := betaCongruence (body := body) (Gamma := [betaF c b i r]) c b i r
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualBoundedCongruenceEquality : InternalBetaCongruenceTargets.ActualBoundedCongruenceEquality := by
  intro body α r s m
  let p := cf r s m ⊓ (ltF r m ⊓ ltF s m)
  have h : Derivation body [p] p := Derivation.hypothesis List.mem_cons_self
  obtain ⟨e⟩ := boundedCongruenceEquality r s m ⟨Derivation.conjunctionLeft h⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight h)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight h)⟩
  rw [onEquality]
  exact ⟨Derivation.implicationIntroduction e⟩

theorem actualBoundedCongruenceBeta : InternalBetaCongruenceTargets.ActualBoundedCongruenceBeta := by
  intro body α c b i r
  let p := cf c r (modulus b i) ⊓ ltF r (modulus b i)
  have h : Derivation body [p] p := Derivation.hypothesis List.mem_cons_self
  obtain ⟨h⟩ := boundedCongruenceBeta c b i r ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionRight h⟩
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCongruenceProof
