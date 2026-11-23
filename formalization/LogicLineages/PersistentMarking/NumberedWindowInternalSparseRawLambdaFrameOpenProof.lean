module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaFrameTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaFrameOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalControlGraphSupportProof (compositionValue successorValue)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept constantZeroValue)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalitySelf)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePairGraphProof (consGraph)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (Reports)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw frameSlot sameSlot)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalSparseRawLambdaFrame

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem endpointReports (dom child : OTerm α) :
    let n := endpointTerm dom child
    Nonempty (Derivation B Γ (unary termShape (suc z) n)) ∧ Reports B Γ n cellTail [dom,child] := by
  let n := endpointTerm dom child
  have tag : Nonempty (Derivation B Γ (unary (literal 1 2) (numeral 2) n)) := literalGraph 2 ![n]
  exact packedNode (literal 1 2) (numeral 2) [dom,child] tag

private theorem witnessReport (child : OTerm α) :
    let n := witnessTerm child
    Nonempty (Derivation B Γ (unary witnessShape (suc z) n)) ∧ Reports B Γ n cellTail [child] := by
  let n := witnessTerm child
  have tag : Nonempty (Derivation B Γ (unary (literal 1 1) (numeral 1) n)) := literalGraph 1 ![n]
  exact packedNode (literal 1 1) (numeral 1) [child] tag

abbrev At (p : Program 3) (out : OTerm α) (xs : Fin 3 → OTerm α) : Prop :=
  Nonempty (Derivation B Γ (programGraph p out xs))

structure Ready (B : Positive (Fin 1)) (Γ : List (Formula α)) (xs : Fin 3 → OTerm α) (src child dst : OTerm α) : Prop where
  guard : At (B := B) (Γ := Γ) frameGood (suc z) xs
  source : At (B := B) (Γ := Γ) (frameSlot 1 0) src xs
  witness : At (B := B) (Γ := Γ) (frameSlot 0 1) child xs
  target : At (B := B) (Γ := Γ) (frameSlot 1 2) dst xs

theorem literalReports (dom src child dst : OTerm α) :
    Ready (B := B) (Γ := Γ) (liftedTape dom src child dst) src child dst := by
  let xs := liftedTape dom src child dst
  obtain ⟨L,l⟩ := endpointReports (B := B) (Γ := Γ) dom src
  obtain ⟨R,r⟩ := endpointReports (B := B) (Γ := Γ) dom dst
  obtain ⟨M,m⟩ := witnessReport (B := B) (Γ := Γ) child
  have left := onTape (field 0) 0 dom xs l.1
  have right := onTape (field 0) 2 dom xs r.1
  have same : At (B := B) (Γ := Γ) (sameSlot 0) (suc z) xs := by
    unfold sameSlot
    apply compositionValue equalityTest ![frameSlot 0 0,frameSlot 0 2] (suc z) xs ![dom,dom]
      (equalitySelf dom)
    intro k
    exact Fin.cases left (Fin.cases right (fun e => Fin.elim0 e)) k
  have good : At (B := B) (Γ := Γ) frameGood (suc z) xs :=
    conjunctionAccept (onRaw witnessShape 1) _ xs (onTape witnessShape 1 (suc z) xs M)
      (conjunctionAccept (onRaw termShape 0) _ xs (onTape termShape 0 (suc z) xs L)
        (conjunctionAccept (onRaw termShape 2) (sameSlot 0) xs (onTape termShape 2 (suc z) xs R) same))
  exact ⟨good,onTape (field 1) 0 src xs l.2.1,onTape (field 0) 1 child xs m.1,
    onTape (field 1) 2 dst xs r.2.1⟩

private theorem consOfGraph (p q : Program 3) (h t : OTerm α) (xs : Fin 3 → OTerm α)
    (left : At (B := B) (Γ := Γ) p h xs) (right : At (B := B) (Γ := Γ) q t xs) :
    At (B := B) (Γ := Γ) (consOf p q) (rawCons h t) xs := by
  unfold At consOf
  apply compositionValue fieldCons (Fin.cons p (Fin.cons q Fin.elim0)) (rawCons h t) xs ![h,t]
    (consGraph h t)
  intro i
  exact Fin.cases left (Fin.cases right (fun e => Fin.elim0 e)) i

private theorem emit (xs : Fin 3 → OTerm α) (src child dst : OTerm α)
    (facts : Ready (B := B) (Γ := Γ) xs src child dst) :
    At (B := B) (Γ := Γ) emitFrame (frameValueTerm src child dst) xs := by
  let a := consOf (frameSlot 1 2) (constantZero 3)
  let b := consOf (frameSlot 0 1) a
  let c := consOf (frameSlot 1 0) b
  let ta := rawCons dst z
  let tb := rawCons child ta
  let tc := rawCons src tb
  have ha : At (B := B) (Γ := Γ) a ta xs :=
    consOfGraph (frameSlot 1 2) (constantZero 3) dst z xs facts.target (constantZeroValue xs)
  have hb : At (B := B) (Γ := Γ) b tb xs :=
    consOfGraph (frameSlot 0 1) a child ta xs facts.witness ha
  have hc : At (B := B) (Γ := Γ) c tc xs :=
    consOfGraph (frameSlot 1 0) b src tb xs facts.source hb
  unfold At emitFrame frameValueTerm
  apply compositionValue .succ (fun _ : Fin 1 => c) (suc tc) xs ![tc] (successorValue ![tc])
  intro k
  obtain rfl := Fin.eq_zero k
  exact hc

theorem exact_OpenLiteralLambdaFrame : ExactOpenLiteralLambdaFrame := by
  intro B α Γ dom src child dst
  let xs := liftedTape dom src child dst
  have facts := literalReports (B := B) (Γ := Γ) dom src child dst
  exact successorBranchIntro frameGood (constantZero 3) emitFrame
    (frameValueTerm src child dst) z xs facts.guard (emit xs src child dst facts)

#print axioms literalReports
#print axioms exact_OpenLiteralLambdaFrame
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaFrameOpenProof
