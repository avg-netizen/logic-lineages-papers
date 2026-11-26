module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoGuardedTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoLiftChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoGuardedChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover conjunctionAccept)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalAuxExchangeMemoStepTargets (step)
open NumberedWindowInternalAuxExchangeMemoLiftTargets (syntaxOne)
open NumberedWindowInternalAuxExchangeMemoLiftChecks (derive)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseSymmetricExchangeTargets (swapExchange pairedExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange compareOptions optionAtSlot)
open NumberedWindowInternalSparseCoverScratch (coverOption)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalAuxExchangeMemoGuardedTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem swapArgs (a b : OTerm α) :
    ∀ i : Fin 2, Nonempty (Derivation body Γ (programGraph
      ((![.projection 1,.projection 0] : Fin 2 → Program 2) i)
      ((![b,a] : Fin 2 → OTerm α) i) ![a,b])) := by
  intro i
  exact Fin.cases (projectionValue 1 ![a,b])
    (Fin.cases (projectionValue 0 ![a,b]) (fun j => Fin.elim0 j)) i

private theorem swapValue (X : Program 2) (a b : OTerm α) :
    Nonempty (Derivation body Γ (accepted (swapExchange X) a b)) ↔
    Nonempty (Derivation body Γ (accepted X b a)) := by
  constructor
  · intro h
    exact compositionRecover X ![.projection 1,.projection 0] (suc z) ![a,b] ![b,a] h (swapArgs a b)
  · intro h
    exact compositionValue X ![.projection 1,.projection 0] (suc z) ![a,b] ![b,a] h (swapArgs a b)

private theorem pairDerive (base : Program 2) (V : Program 1) (dom cod fn fn' arg : OTerm α)
    (child : Nonempty (Derivation body Γ (accepted (paired base V) fn fn')))
    (left : Nonempty (Derivation body Γ (syntaxOne V (auxiliaryTerm dom cod fn arg))))
    (right : Nonempty (Derivation body Γ (syntaxOne V (auxiliaryTerm dom cod fn' arg)))) :
    Nonempty (Derivation body Γ (accepted (paired base V)
      (auxiliaryTerm dom cod fn arg) (auxiliaryTerm dom cod fn' arg))) := by
  let X := selected (step base V)
  let a := auxiliaryTerm dom cod fn arg
  let b := auxiliaryTerm dom cod fn' arg
  obtain ⟨both⟩ := conjunctionRecover X (swapExchange X) ![fn,fn'] child
  have reverse := (swapValue X fn fn').mp ⟨Derivation.conjunctionRight both⟩
  have forward := derive base V dom cod fn fn' arg ⟨Derivation.conjunctionLeft both⟩ left right
  have backward := derive base V dom cod fn' fn arg reverse right left
  exact conjunctionAccept X (swapExchange X) ![a,b] forward ((swapValue X a b).mpr backward)

private theorem coverSlot (C : Program 3) (s : Settings) (i : Fin 2) (xs : Fin 2 → OTerm α) (out : OTerm α)
    (h : Nonempty (Derivation body Γ (unary (coverOption C s) out (xs i)))) :
    Nonempty (Derivation body Γ (programGraph (optionAtSlot C s i) out xs)) := by
  apply compositionValue (coverOption C s) (fun _ : Fin 1 => .projection i) out xs ![xs i] h
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue i xs

private theorem compareOfEqual (C : Program 3) (s : Settings) (a b x y : OTerm α)
    (one : Nonempty (Derivation body Γ (unary (coverOption C s) x a)))
    (two : Nonempty (Derivation body Γ (unary (coverOption C s) y b)))
    (same : Nonempty (Derivation body Γ (eqn x y))) :
    Nonempty (Derivation body Γ (accepted (compareOptions C s) a b)) := by
  apply compositionValue equalityTest ![optionAtSlot C s 0,optionAtSlot C s 1]
    (suc z) ![a,b] ![x,y] (equalityOfEqual x y same)
  intro i
  exact Fin.cases (coverSlot C s 0 ![a,b] x one)
    (Fin.cases (coverSlot C s 1 ![a,b] y two) (fun k => Fin.elim0 k)) i

theorem exact_OpenPairedAuxMemoLift : ExactOpenPairedAuxMemoLift := by
  intro base V body α Γ dom cod fn fn' arg a b
  let h := accepted (paired base V) fn fn' ⊓ (syntaxOne V a ⊓ syntaxOne V b)
  have input : Derivation body (h :: Γ) h := Derivation.hypothesis List.mem_cons_self
  obtain ⟨out⟩ := pairDerive base V dom cod fn fn' arg ⟨Derivation.conjunctionLeft input⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight input)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight input)⟩
  exact ⟨Derivation.implicationIntroduction out⟩

theorem exact_OpenGuardedAuxMemoLift : ExactOpenGuardedAuxMemoLift := by
  intro C s base V body α Γ dom cod fn fn' arg outA outB a b X parentCovers
  let h := accepted X fn fn' ⊓ ((syntaxOne V a ⊓ syntaxOne V b) ⊓ parentCovers)
  let Δ := h :: Γ
  have input : Derivation body Δ h := Derivation.hypothesis List.mem_cons_self
  obtain ⟨pairAndCover⟩ := conjunctionRecover (paired base V) (compareOptions C s) ![fn,fn']
    ⟨Derivation.conjunctionLeft input⟩
  have facts := Derivation.conjunctionRight input
  have syntaxReports := Derivation.conjunctionLeft facts
  have options := Derivation.conjunctionRight facts
  have edge := pairDerive base V dom cod fn fn' arg ⟨Derivation.conjunctionLeft pairAndCover⟩
    ⟨Derivation.conjunctionLeft syntaxReports⟩ ⟨Derivation.conjunctionRight syntaxReports⟩
  have covers := compareOfEqual C s a b outA outB ⟨Derivation.conjunctionLeft options⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight options)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight options)⟩
  obtain ⟨out⟩ := conjunctionAccept (paired base V) (compareOptions C s) ![a,b] edge covers
  exact ⟨Derivation.implicationIntroduction out⟩

#print axioms exact_OpenPairedAuxMemoLift
#print axioms exact_OpenGuardedAuxMemoLift

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoGuardedChecks
