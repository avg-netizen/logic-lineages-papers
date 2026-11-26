module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentHeadBranches.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.ApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentHeadBranches.FactorsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ExchangeLayer ExchangeLayer.InternalSupportProof ExchangeLayer.ApplicationProof
variable {body : Positive (Fin 1)} {alpha : Type}
attribute [local irreducible] programGraph

def Factor (p : Program 19) (xs : Fin 19 → OTerm alpha) (F : Formula alpha) : Prop :=
  ∀ Delta, Nonempty (Derivation body Delta (programGraph p (numeral 1) xs)) ↔
    Nonempty (Derivation body Delta F)

theorem eqFactor (i j : Fin 19) (xs : Fin 19 → OTerm alpha) :
    Factor (body:=body) (eqField i j) xs (eqn (xs i) (xs j)) :=
  fun _ => ⟨eqRecover i j xs,eqAccept i j xs⟩

theorem projectionFactor (i : Fin 19) (xs : Fin 19 → OTerm alpha) :
    Factor (body:=body) (.projection i) xs (eqn (xs i) (numeral 1)) :=
  fun _ => ⟨projectionRecover i xs,projectionAt i xs (numeral 1)⟩

theorem bothFactor (p q : Program 19) (xs : Fin 19 → OTerm alpha) (F G : Formula alpha)
    (hp : Factor (body:=body) p xs F) (hq : Factor (body:=body) q xs G) :
    Factor (body:=body) (both p q) xs (F ⊓ G) := by
  intro Delta
  constructor
  · intro h
    obtain ⟨h⟩ := bothRecover p q xs h
    obtain ⟨hf⟩ := (hp Delta).mp ⟨Derivation.conjunctionLeft h⟩
    obtain ⟨hg⟩ := (hq Delta).mp ⟨Derivation.conjunctionRight h⟩
    exact ⟨Derivation.conjunctionIntroduction hf hg⟩
  · rintro ⟨h⟩
    exact bothAccept p q xs ((hp Delta).mpr ⟨Derivation.conjunctionLeft h⟩)
      ((hq Delta).mpr ⟨Derivation.conjunctionRight h⟩)

theorem anyFactor (p q : Program 19) (xs : Fin 19 → OTerm alpha) (F G : Formula alpha)
    (hp : Factor (body:=body) p xs F) (hq : Factor (body:=body) q xs G) :
    Factor (body:=body) (any p q) xs (F ⊔ G) := by
  intro Delta
  constructor
  · intro h
    obtain ⟨h⟩ := anyRecover p q xs h
    obtain ⟨hf⟩ := (hp (programGraph p (numeral 1) xs :: Delta)).mp ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hg⟩ := (hq (programGraph q (numeral 1) xs :: Delta)).mp ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨disjunctionElimination h (Derivation.implicationIntroduction (orLeft hf))
      (Derivation.implicationIntroduction (orRight hg))⟩
  · rintro ⟨h⟩
    obtain ⟨hf⟩ := anyLeft p q xs ((hp (F :: Delta)).mpr ⟨Derivation.hypothesis List.mem_cons_self⟩)
    obtain ⟨hg⟩ := anyRight p q xs ((hq (G :: Delta)).mpr ⟨Derivation.hypothesis List.mem_cons_self⟩)
    exact ⟨disjunctionElimination h (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hg)⟩

theorem ordinaryFactor (xs : Fin 19 → OTerm alpha) :
    Factor (body:=body) ordinaryCase xs
      ((eqn (xs 16) (numeral 1) ⊓ eqn (xs 18) (xs 17)) ⊔
       (eqn (xs 2) (xs 9) ⊓ eqn (xs 14) (numeral 1))) :=
  anyFactor _ _ xs _ _
    (bothFactor _ _ xs _ _ (projectionFactor 16 xs) (eqFactor 18 17 xs))
    (bothFactor _ _ xs _ _ (eqFactor 2 9 xs) (projectionFactor 14 xs))

theorem numberedFactor (xs : Fin 19 → OTerm alpha) :
    Factor (body:=body) numberedCase xs
      ((eqn (xs 3) (xs 10) ⊓ (eqn (xs 1) (xs 8) ⊓ eqn (xs 4) (xs 11))) ⊓
       (((eqn (xs 6) (xs 13) ⊓ eqn (xs 16) (numeral 1)) ⊔
         ((eqn (xs 2) (xs 9) ⊓ eqn (xs 6) (xs 13)) ⊓ eqn (xs 14) (numeral 1))) ⊔
        ((eqn (xs 2) (xs 9) ⊓ eqn (xs 5) (xs 12)) ⊓ eqn (xs 15) (numeral 1)))) :=
  bothFactor _ _ xs _ _
    (bothFactor _ _ xs _ _ (eqFactor 3 10 xs)
      (bothFactor _ _ xs _ _ (eqFactor 1 8 xs) (eqFactor 4 11 xs)))
    (anyFactor _ _ xs _ _
      (anyFactor _ _ xs _ _
        (bothFactor _ _ xs _ _ (eqFactor 6 13 xs) (projectionFactor 16 xs))
        (bothFactor _ _ xs _ _
          (bothFactor _ _ xs _ _ (eqFactor 2 9 xs) (eqFactor 6 13 xs)) (projectionFactor 14 xs)))
      (bothFactor _ _ xs _ _
        (bothFactor _ _ xs _ _ (eqFactor 2 9 xs) (eqFactor 5 12 xs)) (projectionFactor 15 xs)))

theorem dispatchOrdinary (Delta : List (Formula alpha)) (xs : Fin 19 → OTerm alpha)
    (hx : Nonempty (Derivation body Delta (eqn (xs 0) (numeral 4))))
    (hy : Nonempty (Derivation body Delta (eqn (xs 7) (numeral 4)))) :
    Nonempty (Derivation body Delta (programGraph layer (numeral 1) xs)) ↔
    Nonempty (Derivation body Delta (programGraph ordinaryCase (numeral 1) xs)) := by
  have hc := chooseAccept (eqField 0 7) dispatch (InternalAcceptance.constantZero 19) xs (sameTag xs 4 hx hy)
  let rest := choose (tagIs 4) ordinaryCase (choose (tagIs 5) numberedCase
    (choose (tagIs 7) applicationCase (InternalAcceptance.constantZero 19)))
  have h1 := chooseNumeral 4 1 lambdaCase afterLambda xs hx
  have h2 := chooseNumeral 4 2 applicationCase rest xs hx
  have h4 := chooseNumeral 4 4 ordinaryCase (choose (tagIs 5) numberedCase
    (choose (tagIs 7) applicationCase (InternalAcceptance.constantZero 19))) xs hx
  simp only [show ¬(4 = 1) by decide,show ¬(4 = 2) by decide,ite_false,ite_true] at h1 h2 h4
  exact hc.trans (h1.trans (h2.trans h4))

theorem dispatchNumbered (Delta : List (Formula alpha)) (xs : Fin 19 → OTerm alpha)
    (hx : Nonempty (Derivation body Delta (eqn (xs 0) (numeral 5))))
    (hy : Nonempty (Derivation body Delta (eqn (xs 7) (numeral 5)))) :
    Nonempty (Derivation body Delta (programGraph layer (numeral 1) xs)) ↔
    Nonempty (Derivation body Delta (programGraph numberedCase (numeral 1) xs)) := by
  have hc := chooseAccept (eqField 0 7) dispatch (InternalAcceptance.constantZero 19) xs (sameTag xs 5 hx hy)
  let rest := choose (tagIs 4) ordinaryCase (choose (tagIs 5) numberedCase
    (choose (tagIs 7) applicationCase (InternalAcceptance.constantZero 19)))
  have h1 := chooseNumeral 5 1 lambdaCase afterLambda xs hx
  have h2 := chooseNumeral 5 2 applicationCase rest xs hx
  have h4 := chooseNumeral 5 4 ordinaryCase (choose (tagIs 5) numberedCase
    (choose (tagIs 7) applicationCase (InternalAcceptance.constantZero 19))) xs hx
  have h5 := chooseNumeral 5 5 numberedCase (choose (tagIs 7) applicationCase (InternalAcceptance.constantZero 19)) xs hx
  simp only [show ¬(5 = 1) by decide,show ¬(5 = 2) by decide,show ¬(5 = 4) by decide,ite_false,ite_true] at h1 h2 h4 h5
  exact hc.trans (h1.trans (h2.trans (h4.trans h5)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentHeadBranches.FactorsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentHeadBranches.FactorsProof
