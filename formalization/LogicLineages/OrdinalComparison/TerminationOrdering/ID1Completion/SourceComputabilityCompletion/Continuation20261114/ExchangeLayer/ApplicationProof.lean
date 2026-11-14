module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.InternalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TypedPrimaryEdge.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.ApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof InternalAcceptanceNormalizationProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
abbrev OT := InternalGraphComposition.OTerm

open InternalSupportProof
open InternalBetaTotalityProof InternalQuotientComparisonProof

theorem anyLeft (p q : Program 19) (xs : Fin 19 → OT alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p (suc z) xs))) :
    Nonempty (Derivation body Delta (programGraph (any p q) (suc z) xs)) :=
  successorBranchIntro _ _ _ (suc z) z xs (normalizeAccept p xs hp) (normalizeAccept p xs hp)

theorem anyRight (p q : Program 19) (xs : Fin 19 → OT alpha)
    (hq : Nonempty (Derivation body Delta (programGraph q (suc z) xs))) :
    Nonempty (Derivation body Delta (programGraph (any p q) (suc z) xs)) := by
  let A := programGraph p (suc z) xs
  apply formulaCases A
  · exact anyLeft p q xs ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact zeroBranchIntro _ _ _ (suc z) xs
      (normalizeReject p xs ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (normalizeAccept q xs (withHyp hq A.not))

theorem anyRecover (p q : Program 19) (xs : Fin 19 → OT alpha)
    (h : Nonempty (Derivation body Delta (programGraph (any p q) (suc z) xs))) :
    Nonempty (Derivation body Delta (programGraph p (suc z) xs ⊔ programGraph q (suc z) xs)) := by
  let A := programGraph p (suc z) xs
  apply formulaCases A
  · exact ⟨orLeft (Derivation.hypothesis List.mem_cons_self)⟩
  · have hq := zeroBranchElim _ _ _ (suc z) xs
      (normalizeReject p xs ⟨Derivation.hypothesis List.mem_cons_self⟩) (withHyp h A.not)
    obtain ⟨hq⟩ := normalizeRecover q xs hq
    exact ⟨orRight hq⟩

theorem pairRecover (i j k : Fin 19) (xs : Fin 19 → OT alpha)
    (h : Nonempty (Derivation body Delta (programGraph (both (eqField i j) (.projection k)) (suc z) xs))) :
    Nonempty (Derivation body Delta (eqn (xs i) (xs j) ⊓ eqn (xs k) (suc z))) := by
  obtain ⟨h⟩ := bothRecover (eqField i j) (.projection k) xs h
  obtain ⟨he⟩ := eqRecover i j xs ⟨Derivation.conjunctionLeft h⟩
  obtain ⟨hk⟩ := projectionRecover k xs ⟨Derivation.conjunctionRight h⟩
  exact ⟨Derivation.conjunctionIntroduction he hk⟩

theorem pairAccept (i j k : Fin 19) (xs : Fin 19 → OT alpha)
    (h : Nonempty (Derivation body Delta (eqn (xs i) (xs j) ⊓ eqn (xs k) (suc z)))) :
    Nonempty (Derivation body Delta (programGraph (both (eqField i j) (.projection k)) (suc z) xs)) := by
  obtain ⟨h⟩ := h
  exact bothAccept (eqField i j) (.projection k) xs
    (eqAccept i j xs ⟨Derivation.conjunctionLeft h⟩)
    (projectionAt k xs (suc z) ⟨Derivation.conjunctionRight h⟩)

theorem applicationFactor (xs : Fin 19 → OT alpha) :
    (Nonempty (Derivation body Delta (programGraph applicationCase (suc z) xs)) ↔
     Nonempty (Derivation body Delta (eqn (xs 1) (xs 8) ⊓
       ((eqn (xs 6) (xs 13) ⊓ eqn (xs 14) (suc z)) ⊔
        (eqn (xs 5) (xs 12) ⊓ eqn (xs 15) (suc z)))))) := by
  let p := both (eqField 6 13) (.projection 14)
  let q := both (eqField 5 12) (.projection 15)
  constructor
  · intro h
    obtain ⟨hh⟩ := bothRecover (eqField 1 8) (any p q) xs h
    obtain ⟨ha⟩ := eqRecover 1 8 xs ⟨Derivation.conjunctionLeft hh⟩
    obtain ⟨hd⟩ := anyRecover p q xs ⟨Derivation.conjunctionRight hh⟩
    obtain ⟨hl⟩ := pairRecover (body:=body) (Delta:=programGraph p (suc z) xs :: Delta) 6 13 14 xs
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hr⟩ := pairRecover (body:=body) (Delta:=programGraph q (suc z) xs :: Delta) 5 12 15 xs
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.conjunctionIntroduction ha (disjunctionElimination hd
      (Derivation.implicationIntroduction (orLeft hl)) (Derivation.implicationIntroduction (orRight hr)))⟩
  · rintro ⟨h⟩
    apply bothAccept (eqField 1 8) (any p q) xs
    · exact eqAccept 1 8 xs ⟨Derivation.conjunctionLeft h⟩
    · let A := eqn (xs 6) (xs 13) ⊓ eqn (xs 14) (suc z)
      let B := eqn (xs 5) (xs 12) ⊓ eqn (xs 15) (suc z)
      obtain ⟨hl⟩ := anyLeft p q xs
        (pairAccept (body:=body) (Delta:=A :: Delta) 6 13 14 xs ⟨Derivation.hypothesis List.mem_cons_self⟩)
      obtain ⟨hr⟩ := anyRight p q xs
        (pairAccept (body:=body) (Delta:=B :: Delta) 5 12 15 xs ⟨Derivation.hypothesis List.mem_cons_self⟩)
      exact ⟨disjunctionElimination (Derivation.conjunctionRight h)
        (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction hr)⟩

theorem internalApplication : Targets.InternalApplication := by
  intro body alpha Delta xs tag htag hx hy
  have hs := sameTag xs tag hx hy
  have hc := chooseAccept (eqField 0 7) dispatch (InternalAcceptance.constantZero 19) xs hs
  let rest2 := choose (tagIs 4) ordinaryCase (choose (tagIs 5) numberedCase
    (choose (tagIs 7) applicationCase (InternalAcceptance.constantZero 19)))
  rcases htag with rfl | rfl
  · have h1 := chooseNumeral 2 1 lambdaCase afterLambda xs hx
    have h2 := chooseNumeral 2 2 applicationCase rest2 xs hx
    simp only [show ¬(2 = 1) by decide,ite_false,ite_true] at h1 h2
    exact hc.trans (h1.trans (h2.trans (applicationFactor xs)))
  · have h1 := chooseNumeral 7 1 lambdaCase afterLambda xs hx
    have h2 := chooseNumeral 7 2 applicationCase rest2 xs hx
    have h4 := chooseNumeral 7 4 ordinaryCase (choose (tagIs 5) numberedCase
      (choose (tagIs 7) applicationCase (InternalAcceptance.constantZero 19))) xs hx
    have h5 := chooseNumeral 7 5 numberedCase
      (choose (tagIs 7) applicationCase (InternalAcceptance.constantZero 19)) xs hx
    have h7 := chooseNumeral 7 7 applicationCase (InternalAcceptance.constantZero 19) xs hx
    simp only [show ¬(7 = 1) by decide,show ¬(7 = 2) by decide,show ¬(7 = 4) by decide,
      show ¬(7 = 5) by decide,ite_false,ite_true] at h1 h2 h4 h5 h7
    exact hc.trans (h1.trans (h2.trans (h4.trans (h5.trans (h7.trans (applicationFactor xs))))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.ApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.ApplicationProof
