module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalScanSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalScanSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalTransparentMinimum OriginalTransparentMinimumInternalScanSyntaxProof
open InternalGraphComposition InternalAcceptanceSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding OTerm
open InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalQuotientComparisonProof
open InternalSquareRootArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalSourceInversionSupportProof InternalLeastNumberProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem resultTransport (Q : Program 3) (bound seed parameter earlier s t : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn s t)))
    (h : Nonempty (Derivation body Gamma (resultFormula Q bound seed parameter s earlier))) :
    Nonempty (Derivation body Gamma (resultFormula Q bound seed parameter t earlier)) := by
  obtain ⟨he⟩ := he
  obtain ⟨h⟩ := h
  have d := Derivation.equalityElimination
    (resultFormula Q (bound.relabel Sum.inl) (seed.relabel Sum.inl)
      (parameter.relabel Sum.inl) (.var (.inr 0)) (earlier.relabel Sum.inl))
    (emb s) (emb t) he
  simp only [resultInstantiate,varBind,liftBind] at d
  exact ⟨d h⟩

theorem candidateTransport (Q : Program 3) (seed parameter s t : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn s t)))
    (h : Nonempty (Derivation body Gamma (graph3 Q (suc z) seed s parameter))) :
    Nonempty (Derivation body Gamma (graph3 Q (suc z) seed t parameter)) := by
  apply InternalGraphCompositionEqualityProof.graphInputTransport body α 3 Gamma _ (suc z)
    (Fin.cons seed (Fin.cons s (Fin.cons parameter Fin.elim0)))
    (Fin.cons seed (Fin.cons t (Fin.cons parameter Fin.elim0))) _ h
  intro i
  rw [onEquality]
  exact Fin.cases ⟨refl _⟩ (Fin.cases he (Fin.cases ⟨refl _⟩ (fun j => Fin.elim0 j))) i

theorem boundEquality (previous bound : OTerm α)
    (hb : Nonempty (Derivation body Gamma (ltF previous (suc bound))))
    (hn : Nonempty (Derivation body Gamma (ltF previous bound).not)) :
    Nonempty (Derivation body Gamma (eqn previous bound)) := by
  obtain ⟨hb⟩ := hb
  obtain ⟨hn⟩ := hn
  obtain ⟨split⟩ := actualRightSuccessorSplit body α previous bound
  rw [onEquality] at split
  have hs := Derivation.implicationElimination (weakenClosed split Gamma) hb
  exact ⟨disjunctionElimination hs
    (Derivation.implicationIntroduction (Derivation.explosion
      (Derivation.implicationElimination (addHyp hn _) (Derivation.hypothesis List.mem_cons_self))))
    (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))⟩

theorem resultZero (Q : Program 3) (seed parameter earlier : OTerm α) :
    Nonempty (Derivation body Gamma (resultFormula Q z seed parameter z earlier)) := by
  obtain ⟨hz⟩ := actualNothingBelowZero body α (z : OTerm α)
  obtain ⟨he⟩ := actualNothingBelowZero body α earlier
  have hh : Derivation body Gamma ((ltF z z).imp (graph3 Q (suc z) seed z parameter)) :=
    Derivation.implicationIntroduction (Derivation.explosion
      (Derivation.implicationElimination (weakenClosed hz _) (Derivation.hypothesis List.mem_cons_self)))
  have hm : Derivation body Gamma ((ltF earlier z).imp (graph3 Q (suc z) seed earlier parameter).not) :=
    Derivation.implicationIntroduction (Derivation.explosion
      (Derivation.implicationElimination (weakenClosed he _) (Derivation.hypothesis List.mem_cons_self)))
  exact ⟨Derivation.conjunctionIntroduction (equalToNext (refl z))
    (Derivation.conjunctionIntroduction hh hm)⟩

theorem resultRetained (Q : Program 3) (bound seed parameter previous earlier : OTerm α)
    (hi : Nonempty (Derivation body Gamma (resultFormula Q bound seed parameter previous earlier)))
    (hl : Nonempty (Derivation body Gamma (ltF previous bound))) :
    Nonempty (Derivation body Gamma (resultFormula Q (suc bound) seed parameter previous earlier)) := by
  obtain ⟨hi⟩ := hi
  obtain ⟨hl⟩ := hl
  obtain ⟨hb⟩ := rightSuccessor previous (suc bound) ⟨Derivation.conjunctionLeft hi⟩
  have hh := Derivation.implicationElimination (Derivation.conjunctionLeft (Derivation.conjunctionRight hi)) hl
  exact ⟨Derivation.conjunctionIntroduction hb
    (Derivation.conjunctionIntroduction (Derivation.implicationIntroduction (addHyp hh _))
      (Derivation.conjunctionRight (Derivation.conjunctionRight hi)))⟩

theorem resultHit (Q : Program 3) (bound seed parameter previous earlier : OTerm α)
    (hi : Nonempty (Derivation body Gamma (resultFormula Q bound seed parameter previous earlier)))
    (hn : Nonempty (Derivation body Gamma (ltF previous bound).not))
    (hq : Nonempty (Derivation body Gamma (graph3 Q (suc z) seed bound parameter))) :
    Nonempty (Derivation body Gamma (resultFormula Q (suc bound) seed parameter bound earlier)) := by
  obtain ⟨hi⟩ := hi
  obtain ⟨hq⟩ := hq
  obtain ⟨he⟩ := boundEquality previous bound ⟨Derivation.conjunctionLeft hi⟩ hn
  have hm : Derivation body Gamma ((ltF earlier bound).imp (graph3 Q (suc z) seed earlier parameter).not) := by
    have hl : Derivation body (ltF earlier bound :: Gamma) (ltF earlier previous) :=
      orderRight earlier (symm (addHyp he _)) (Derivation.hypothesis List.mem_cons_self)
    exact Derivation.implicationIntroduction (Derivation.implicationElimination
      (addHyp (Derivation.conjunctionRight (Derivation.conjunctionRight hi)) _) hl)
  obtain ⟨hb⟩ := rightSuccessor bound (suc bound) ⟨equalToNext (refl bound)⟩
  exact ⟨Derivation.conjunctionIntroduction hb
    (Derivation.conjunctionIntroduction (Derivation.implicationIntroduction (addHyp hq _)) hm)⟩

theorem missExtend (Q : Program 3) (bound seed parameter earlier : OTerm α)
    (hm : Nonempty (Derivation body Gamma
      ((ltF earlier bound).imp (graph3 Q (suc z) seed earlier parameter).not)))
    (hn : Nonempty (Derivation body Gamma (graph3 Q (suc z) seed bound parameter).not)) :
    Nonempty (Derivation body Gamma
      ((ltF earlier (suc bound)).imp (graph3 Q (suc z) seed earlier parameter).not)) := by
  obtain ⟨hm⟩ := hm
  obtain ⟨hn⟩ := hn
  let L := ltF earlier (suc bound)
  obtain ⟨split⟩ := actualRightSuccessorSplit body α earlier bound
  rw [onEquality] at split
  have hs : Derivation body (L :: Gamma) (ltF earlier bound ⊔ eqn earlier bound) :=
    Derivation.implicationElimination (weakenClosed split _) (Derivation.hypothesis List.mem_cons_self)
  have hl : Derivation body (L :: Gamma)
      ((ltF earlier bound).imp (graph3 Q (suc z) seed earlier parameter).not) := addHyp hm _
  have he : Nonempty (Derivation body (eqn earlier bound :: L :: Gamma)
      (graph3 Q (suc z) seed earlier parameter).not) := by
    obtain ⟨hq⟩ := candidateTransport Q seed parameter earlier bound
      (body := body) (Gamma := graph3 Q (suc z) seed earlier parameter :: eqn earlier bound :: L :: Gamma)
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination
      (addHyp (addHyp (addHyp hn _) _) _) hq)⟩
  obtain ⟨he⟩ := he
  exact ⟨Derivation.implicationIntroduction
    (disjunctionElimination hs hl (Derivation.implicationIntroduction he))⟩

theorem resultMiss (Q : Program 3) (bound seed parameter previous earlier : OTerm α)
    (hi : Nonempty (Derivation body Gamma (resultFormula Q bound seed parameter previous earlier)))
    (hn : Nonempty (Derivation body Gamma (ltF previous bound).not))
    (hq : Nonempty (Derivation body Gamma (graph3 Q (suc z) seed bound parameter).not)) :
    Nonempty (Derivation body Gamma (resultFormula Q (suc bound) seed parameter (suc bound) earlier)) := by
  obtain ⟨hi⟩ := hi
  obtain ⟨he⟩ := boundEquality previous bound ⟨Derivation.conjunctionLeft hi⟩ hn
  have hm : Nonempty (Derivation body Gamma
      ((ltF earlier bound).imp (graph3 Q (suc z) seed earlier parameter).not)) := by
    have hl : Derivation body (ltF earlier bound :: Gamma) (ltF earlier previous) :=
      orderRight earlier (symm (addHyp he _)) (Derivation.hypothesis List.mem_cons_self)
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination
      (addHyp (Derivation.conjunctionRight (Derivation.conjunctionRight hi)) _) hl)⟩
  obtain ⟨hm⟩ := missExtend Q bound seed parameter earlier hm hq
  obtain ⟨irr⟩ := actualOriginalOrderIrreflexivity body α (suc bound)
  have hh : Derivation body Gamma
      ((ltF (suc bound) (suc bound)).imp (graph3 Q (suc z) seed (suc bound) parameter)) :=
    Derivation.implicationIntroduction (Derivation.explosion
      (Derivation.implicationElimination (weakenClosed irr _) (Derivation.hypothesis List.mem_cons_self)))
  exact ⟨Derivation.conjunctionIntroduction (equalToNext (refl (suc bound)))
    (Derivation.conjunctionIntroduction hh hm)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalScanSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalScanSupportProof
