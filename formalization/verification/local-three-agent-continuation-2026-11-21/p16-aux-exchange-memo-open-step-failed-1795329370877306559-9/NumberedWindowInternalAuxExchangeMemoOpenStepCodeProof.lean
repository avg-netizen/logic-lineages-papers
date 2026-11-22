module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumeralEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue successorValue outputTransport valueUnique)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalNumeralEvaluationProof (actualOriginalNumeralEvaluation)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalAuxExchangeMemoStepTargets
open NumberedWindowInternalSparseRawFunctionFrameTargets (functionWitnessTerm)
open NumberedWindowInternalSparsePair (fieldCons pairTerm)
open NumberedWindowInternalSparsePairGraphProof (consGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePairEvaluationProof (consValue)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem unaryGraph (p : Program 1) (q : Program 4) (out value : OTerm α) (xs : Fin 4 → OTerm α)
    (pGraph : Nonempty (Derivation body Γ (programGraph p out ![value])))
    (qGraph : Nonempty (Derivation body Γ (programGraph q value xs))) :
    Nonempty (Derivation body Γ (programGraph (unaryAfter p q) out xs)) := by
  apply compositionValue p (fun _ : Fin 1 => q) out xs ![value] pGraph
  intro i
  obtain rfl := Fin.eq_zero i
  exact qGraph

theorem binaryGraph (p : Program 2) (q r : Program 4) (out left right : OTerm α) (xs : Fin 4 → OTerm α)
    (pGraph : Nonempty (Derivation body Γ (programGraph p out ![left,right])))
    (qGraph : Nonempty (Derivation body Γ (programGraph q left xs)))
    (rGraph : Nonempty (Derivation body Γ (programGraph r right xs))) :
    Nonempty (Derivation body Γ (programGraph (binaryAfter p q r) out xs)) := by
  apply compositionValue p (Fin.cons q (Fin.cons r Fin.elim0)) out xs ![left,right] pGraph
  intro i
  exact Fin.cases qGraph (Fin.cases rGraph (fun j => Fin.elim0 j)) i

structure KeyReports (body : Positive (Fin 1)) (Γ : List (Formula α))
    (xs : Fin 4 → OTerm α) (a b : OTerm α) : Prop where
  current : Nonempty (Derivation body Γ (programGraph currentKey (pairTerm a b) xs))
  valid : Nonempty (Derivation body Γ (programGraph goodKey (suc z) xs))
  source : Nonempty (Derivation body Γ (programGraph rawSource a xs))
  target : Nonempty (Derivation body Γ (programGraph rawTarget b xs))

theorem keyReports (lo old a b : OTerm α)
    (keyEq : Nonempty (Derivation body Γ (eqn (suc lo) (pairTerm a b)))) :
    KeyReports body Γ ![lo,old,z,z] a b := by
  let xs : Fin 4 → OTerm α := ![lo,old,z,z]
  let key := pairTerm a b
  have atSucc : Nonempty (Derivation body Γ (programGraph currentKey (suc lo) xs)) :=
    unaryGraph .succ (.projection 0) (suc lo) lo xs (successorValue ![lo]) (projectionValue 0 xs)
  have atCurrent := outputTransport currentKey (suc lo) key xs keyEq atSucc
  have atPacked : Nonempty (Derivation body Γ (programGraph packedKey (rawCons a b) xs)) :=
    unaryGraph .succ currentKey (suc key) key xs (successorValue ![key]) atCurrent
  obtain ⟨decoded⟩ := canonicalCell (body := body) (Γ := Γ) a b
  have atFlag := unaryGraph cellGood packedKey (suc z) (rawCons a b) xs
    ⟨Derivation.conjunctionLeft decoded⟩ atPacked
  have keyGood := conjunctionAccept (unaryAfter cellGood packedKey) _ xs atFlag (oneConstantValue xs)
  have aGraph := unaryGraph cellHead packedKey a (rawCons a b) xs
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight decoded)⟩ atPacked
  have bGraph := unaryGraph cellTail packedKey b (rawCons a b) xs
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight decoded)⟩ atPacked
  exact ⟨atCurrent,keyGood,aGraph,bGraph⟩

private theorem consNumerals (x y : Nat) :
    Nonempty (Derivation body Γ (programGraph fieldCons
      (numeral (NumberedWindowPairAlgorithm.pair x y + 1)) ![numeral x,numeral y])) := by
  have proof := actualOriginalNumeralEvaluation body 2 fieldCons (x ::ᵥ y ::ᵥ nil) α
  have args : (fun i : Fin 2 => (numeral ((x ::ᵥ y ::ᵥ nil).get i) : OTerm α)) =
      ![numeral x,numeral y] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    obtain rfl := Fin.eq_zero j
    rfl
  rw [consValue x y,args] at proof
  obtain ⟨d⟩ := proof
  exact ⟨weakenClosed d Γ⟩

private theorem dummyEquality :
    Nonempty (Derivation body Γ (eqn (numeral dummyWitnessCode) (functionWitnessTerm (z : OTerm α)))) := by
  let low := rawCons (z : OTerm α) z
  let middle : OTerm α := numeral 1
  have known : Nonempty (Derivation body Γ (programGraph fieldCons middle ![z,z])) := consNumerals 0 0
  obtain ⟨same⟩ := valueUnique fieldCons middle low ![z,z] known (consGraph z z)
  have closedCode : Nonempty (Derivation body Γ (programGraph fieldCons (numeral dummyWitnessCode)
      ![numeral 5,middle])) := consNumerals 5 1
  have moved : Nonempty (Derivation body Γ (programGraph fieldCons (numeral dummyWitnessCode)
      ![numeral 5,low])) := by
    apply graphInputTransport body α 2 Γ (OrdinaryArithmetic.graphFormula fieldCons)
      (numeral dummyWitnessCode) ![numeral 5,middle] ![numeral 5,low] _ closedCode
    intro i
    rw [onEquality]
    exact Fin.cases ⟨refl (numeral 5)⟩ (Fin.cases ⟨same⟩ (fun j => Fin.elim0 j)) i
  exact valueUnique fieldCons (numeral dummyWitnessCode) (functionWitnessTerm z) ![numeral 5,low]
    moved (consGraph (numeral 5) low)

theorem frameGraph (p : Program 3) (out a b : OTerm α) (xs : Fin 4 → OTerm α)
    (key : KeyReports body Γ xs a b)
    (selection : Nonempty (Derivation body Γ (programGraph p out ![a,functionWitnessTerm z,b]))) :
    Nonempty (Derivation body Γ (programGraph (atFrame p) out xs)) := by
  let witness := literal 4 dummyWitnessCode
  have witnessValue : Nonempty (Derivation body Γ (programGraph witness (functionWitnessTerm z) xs)) :=
    outputTransport witness (numeral dummyWitnessCode) (functionWitnessTerm z) xs dummyEquality
      (literalGraph dummyWitnessCode xs)
  apply compositionValue p (Fin.cons rawSource (Fin.cons witness (Fin.cons rawTarget Fin.elim0)))
    out xs ![a,functionWitnessTerm z,b] selection
  intro i
  exact Fin.cases key.source
    (Fin.cases witnessValue (Fin.cases key.target (fun j => Fin.elim0 j))) i

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
