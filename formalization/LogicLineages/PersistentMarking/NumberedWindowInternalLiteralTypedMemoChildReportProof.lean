module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoStageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestSubtractionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoChildReportProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue headTransport)
open ID1Completion.InternalEqualityTest (subtract)
open ID1Completion.InternalEqualityTestSubtractionProof (diagonal)
open ID1Completion.InternalRawListRecursion (lookup)
open ID1Completion.InternalRawListRecursionSyntaxProof (lookupGraph)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons)
open NumberedWindowInternalSparsePair (pair pairTerm)
open NumberedWindowInternalSparsePairGraphProof (pairGraph)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalAuxExchangeMemoStepTargets (binaryAfter)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (binaryGraph unaryGraph)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralTypedAuxEdgeGuardProof (readSlot)
open NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof (exact_OpenEdgeSlotRead)
open NumberedWindowInternalLiteralTypedMemoStageProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem unaryRead (p q : Program 1) (x v y : OTerm α)
    (first : D B Γ (programGraph q v ![x])) (second : D B Γ (programGraph p y ![v])) :
    D B Γ (programGraph (after1 p q) y ![x]) := by
  apply compositionValue p (fun _ : Fin 1 => q) y ![x] ![v] second
  intro i
  obtain rfl := Fin.eq_zero i
  exact first

private theorem carrierFacts (ctx old prev : OTerm α) :
    let data := carrierTerm ctx old prev
    D B Γ (programGraph holdContext ctx ![data]) ∧
      D B Γ (programGraph holdTable old ![data]) ∧ D B Γ (programGraph holdIndex prev ![data]) := by
  let a := rawCons prev z
  let b := rawCons old a
  let data := rawCons ctx b
  obtain ⟨one⟩ := canonicalCell (body := B) (Γ := Γ) prev z
  obtain ⟨two⟩ := canonicalCell (body := B) (Γ := Γ) old a
  obtain ⟨three⟩ := canonicalCell (body := B) (Γ := Γ) ctx b
  have tail1 : D B Γ (programGraph cellTail b ![data]) :=
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight three)⟩
  have tail2 : D B Γ (programGraph (after1 cellTail cellTail) a ![data]) :=
    unaryRead cellTail cellTail data b a tail1 ⟨Derivation.conjunctionRight (Derivation.conjunctionRight two)⟩
  exact ⟨⟨Derivation.conjunctionLeft (Derivation.conjunctionRight three)⟩,
    unaryRead cellHead cellTail data b old tail1 ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight two)⟩,
    unaryRead cellHead (after1 cellTail cellTail) data a prev tail2
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight one)⟩⟩

theorem exact_OpenTypedMemoBaseReport (Base : Program 4) (ctx old prev ty q r : OTerm α)
    (actual : D B Γ (acceptEdge (childOnCarrier Base) (carrierTerm ctx old prev) ty q r)) :
    D B Γ (acceptEdge Base ctx ty q r) := by
  let data := carrierTerm ctx old prev
  let xs : Fin 4 → OTerm α := ![data,ty,q,r]
  let ps : Fin 4 → Program 4 := ![readSlot holdContext 0,.projection 1,.projection 2,.projection 3]
  have context := exact_OpenEdgeSlotRead holdContext 0 xs ctx (carrierFacts (B := B) (Γ := Γ) ctx old prev).1
  obtain ⟨c⟩ := conjunctionRecover (baseOnCarrier Base)
    (conjunction (lookupOnCarrier 2 3) (lookupOnCarrier 3 2)) xs actual
  apply compositionRecover Base ps (suc z) xs ![ctx,ty,q,r] ⟨Derivation.conjunctionLeft c⟩
  exact fun i => Fin.cases context (Fin.cases (projectionValue 1 xs)
    (Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs) (fun j => Fin.elim0 j)))) i

private theorem readRetaped (i j : Fin 4) (ctx old prev ty q r gap : OTerm α)
    (offset : let xs : Fin 4 → OTerm α := ![carrierTerm ctx old prev,ty,q,r]
      D B Γ (eqn (OrdinaryArithmetic.addTerm (pairTerm (xs i) (xs j)) gap) prev))
    (accepted : D B Γ (acceptEdge (lookupOnCarrier i j) (carrierTerm ctx old prev) ty q r)) :
    D B Γ (lookupGraph (suc z) gap old) := by
  let data := carrierTerm ctx old prev
  let xs : Fin 4 → OTerm α := ![data,ty,q,r]
  let key := pairTerm (xs i) (xs j)
  let code := binaryAfter pair (.projection i) (.projection j)
  let lag := binaryAfter subtract code (readSlot holdIndex 0)
  have held := carrierFacts (B := B) (Γ := Γ) ctx old prev
  have idx := exact_OpenEdgeSlotRead holdIndex 0 xs prev held.2.2
  have tab := exact_OpenEdgeSlotRead holdTable 0 xs old held.2.1
  have atKey : D B Γ (programGraph code key xs) := binaryGraph pair (.projection i) (.projection j) key (xs i) (xs j) xs
    (pairGraph (xs i) (xs j)) (projectionValue i xs) (projectionValue j xs)
  have delta : D B Γ (programGraph subtract gap ![key,prev]) := by
    let total := OrdinaryArithmetic.addTerm key gap
    have first : D B Γ (programGraph subtract gap (Fin.cons key (Fin.cons total Fin.elim0))) :=
      diagonal key gap
    have tape : (Fin.cons key (Fin.cons total Fin.elim0) : Fin 2 → OTerm α) = ![key,total] := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
    rw [tape] at first
    unfold programGraph at first ⊢
    apply ID1Completion.InternalGraphCompositionEqualityProof.graphInputTransport B α 2 Γ
      (OrdinaryArithmetic.graphFormula subtract) gap ![key,OrdinaryArithmetic.addTerm key gap]
      ![key,prev] _ first
    intro i
    rw [ID1Completion.InternalSourceInversionSupportProof.onEquality]
    exact Fin.cases (⟨ID1Completion.InternalTagArithmeticSupportProof.refl key⟩ : D B Γ (eqn key key))
      (Fin.cases offset (fun k => Fin.elim0 k)) i
  have lagValue := binaryGraph subtract code (readSlot holdIndex 0) gap key prev xs delta atKey idx
  apply compositionRecover lookup (Fin.cons lag (Fin.cons (readSlot holdTable 0) Fin.elim0))
    (suc z) xs ![gap,old] accepted
  exact fun n => Fin.cases lagValue (Fin.cases tab (fun k => Fin.elim0 k)) n

theorem exact_OpenTypedMemoChildReads (Base : Program 4) (ctx old prev ty q r : OTerm α)
    (actual : D B Γ (acceptEdge (childOnCarrier Base) (carrierTerm ctx old prev) ty q r)) :
    (∀ gap, D B Γ (eqn (OrdinaryArithmetic.addTerm (pairTerm q r) gap) prev) →
      D B Γ (lookupGraph (suc z) gap old)) ∧
    (∀ gap, D B Γ (eqn (OrdinaryArithmetic.addTerm (pairTerm r q) gap) prev) →
      D B Γ (lookupGraph (suc z) gap old)) := by
  let xs : Fin 4 → OTerm α := ![carrierTerm ctx old prev,ty,q,r]
  let f := lookupOnCarrier 2 3
  let r' := lookupOnCarrier 3 2
  obtain ⟨both⟩ := conjunctionRecover (baseOnCarrier Base) (conjunction f r') xs actual
  obtain ⟨parsed⟩ := conjunctionRecover f r' xs ⟨Derivation.conjunctionRight both⟩
  exact ⟨fun gap eq => readRetaped 2 3 ctx old prev ty q r gap eq ⟨Derivation.conjunctionLeft parsed⟩,
    fun gap eq => readRetaped 3 2 ctx old prev ty q r gap eq ⟨Derivation.conjunctionRight parsed⟩⟩

#print axioms exact_OpenTypedMemoBaseReport
#print axioms exact_OpenTypedMemoChildReads
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoChildReportProof
