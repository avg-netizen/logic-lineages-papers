module

public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenCompareProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenComposeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFactoredCoverTargets (rawCall generatorCall factoredCover)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseCoverScratchOpenTargets (callbackTape)
open NumberedWindowInternalSparseCoverScratch (coverOption)
open NumberedWindowInternalSparseCoverScratchOpenSyntaxProof (optionFromCallback)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (pairedExchange swapExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange compareOptions)
open NumberedWindowInternalMeasuredExchangeThinDefinitions (measuredExchange compareMeasurements)
open NumberedWindowInternalMeasuredExchangeThinOpenTargets
open NumberedWindowInternalMeasuredExchangeThinOpenCompareProof (compareShared)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem swappedArgs (a b : OTerm α) :
    ∀ i : Fin 2, Nonempty (Derivation body Γ (programGraph
      ((![.projection 1,.projection 0] : Fin 2 → Program 2) i)
      ((![b,a] : Fin 2 → OTerm α) i) ![a,b])) := by
  intro i
  exact Fin.cases (projectionValue 1 ![a,b])
    (Fin.cases (projectionValue 0 ![a,b]) (fun j => Fin.elim0 j)) i

private theorem swapReports (X : Program 2) (a b : OTerm α) :
    Nonempty (Derivation body Γ (accepted (swapExchange X) a b)) ↔ Nonempty (Derivation body Γ (accepted X b a)) := by
  constructor
  · intro h
    exact compositionRecover X ![.projection 1,.projection 0] (suc z) ![a,b] ![b,a] h (swappedArgs a b)
  · intro h
    exact compositionValue X ![.projection 1,.projection 0] (suc z) ![a,b] ![b,a] h (swappedArgs a b)

theorem recoverChild (M : Program 1) (X : Program 2) (C : Program 3) (s : Settings) (a b : OTerm α)
    (h : Nonempty (Derivation body Γ (accepted (guardedExchange C s (pairedExchange (measuredExchange M X))) a b))) :
    Nonempty (Derivation body Γ (accepted X a b)) ∧ Nonempty (Derivation body Γ (accepted X b a)) ∧
      Nonempty (Derivation body Γ (accepted (compareMeasurements M) a b)) := by
  let Y := measuredExchange M X
  obtain ⟨both⟩ := conjunctionRecover (pairedExchange Y) (compareOptions C s) ![a,b] h
  obtain ⟨pair⟩ := conjunctionRecover Y (swapExchange Y) ![a,b] ⟨Derivation.conjunctionLeft both⟩
  have reverse := (swapReports Y a b).mp ⟨Derivation.conjunctionRight pair⟩
  obtain ⟨left⟩ := conjunctionRecover X (compareMeasurements M) ![a,b] ⟨Derivation.conjunctionLeft pair⟩
  obtain ⟨right⟩ := conjunctionRecover X (compareMeasurements M) ![b,a] reverse
  exact ⟨⟨Derivation.conjunctionLeft left⟩,⟨Derivation.conjunctionLeft right⟩,⟨Derivation.conjunctionRight left⟩⟩

abbrev grammarTape {α : Type} (s : Settings) (m : OTerm α) : Fin 3 → OTerm α :=
  ![numeral (Encodable.encode s.window.2),numeral (Encodable.encode s.types),m]

private theorem atRaw (p : Program 1) (s : Settings) (value raw : OTerm α)
    (h : Nonempty (Derivation body Γ (unary p value raw))) :
    Nonempty (Derivation body Γ (programGraph (rawCall p) value (callbackTape s raw))) := by
  apply compositionValue p (fun _ : Fin 1 => .projection (2 : Fin 3)) value (callbackTape s raw) ![raw] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue (2 : Fin 3) (callbackTape s raw)

theorem putCover (V M : Program 1) (G : Program 3) (s : Settings) (out raw m : OTerm α)
    (valid : Nonempty (Derivation body Γ (unary V (suc z) raw)))
    (measure : Nonempty (Derivation body Γ (unary M m raw)))
    (grammar : Nonempty (Derivation body Γ (programGraph G out (grammarTape s m)))) :
    Nonempty (Derivation body Γ (unary (coverOption (factoredCover V M G) s) out raw)) := by
  let xs := callbackTape s raw
  have branchOut : Nonempty (Derivation body Γ (programGraph (generatorCall M G) out xs)) := by
    apply compositionValue G
      (Fin.cons (.projection 0) (Fin.cons (.projection 1) (Fin.cons (rawCall M) Fin.elim0)))
      out xs (grammarTape s m) grammar
    intro i
    exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
      (Fin.cases (atRaw M s m raw measure) (fun k => Fin.elim0 k))) i
  exact optionFromCallback (factoredCover V M G) s out raw
    (successorBranchIntro (rawCall V) (constantZero 3) (generatorCall M G) out z xs
      (atRaw V s (suc z) raw valid) branchOut)

theorem composeParents (M : Program 1) (X : Program 2) (C : Program 3) (s : Settings)
    (a b m out : OTerm α)
    (forward : Nonempty (Derivation body Γ (accepted X a b)))
    (backward : Nonempty (Derivation body Γ (accepted X b a)))
    (first : Nonempty (Derivation body Γ (unary M m a)))
    (second : Nonempty (Derivation body Γ (unary M m b)))
    (optionA : Nonempty (Derivation body Γ (unary (coverOption C s) out a)))
    (optionB : Nonempty (Derivation body Γ (unary (coverOption C s) out b))) :
    Nonempty (Derivation body Γ (accepted (guardedExchange C s (pairedExchange (measuredExchange M X))) a b)) := by
  let Y := measuredExchange M X
  have direct := conjunctionAccept X (compareMeasurements M) ![a,b] forward (compareShared M a b m first second)
  have reversed := conjunctionAccept X (compareMeasurements M) ![b,a] backward (compareShared M b a m second first)
  have pair := conjunctionAccept Y (swapExchange Y) ![a,b] direct ((swapReports Y a b).mpr reversed)
  have options : Nonempty (Derivation body Γ (accepted (compareOptions C s) a b)) :=
    compareShared (coverOption C s) a b out optionA optionB
  exact conjunctionAccept (pairedExchange Y) (compareOptions C s) ![a,b] pair options

end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenComposeProof
