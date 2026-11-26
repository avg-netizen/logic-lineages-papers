module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalControlGraphProof (actualOriginalZeroTestGraph zeroTestAtZero)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl sucNeZeroApply)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparseFieldCellTargets (certifiedCell)
open NumberedWindowInternalSparseFieldCellSuccessProof (consToCell cellToCons)
open NumberedWindowInternalSparsePairGraphProof (consGraph consEquation)
open NumberedWindowInternalSparsePathEnvelope
open NumberedWindowInternalSparsePathEnvelopeTargets
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem canonicalCell (h t : OTerm α) :
    Nonempty (Derivation body Γ (certifiedCell (rawCons h t) h t)) :=
  consToCell (rawCons h t) h t (consGraph h t)

theorem cellEquation (n h t : OTerm α)
    (g : Nonempty (Derivation body Γ (unary cellGood (suc z) n)))
    (a : Nonempty (Derivation body Γ (unary cellHead h n)))
    (b : Nonempty (Derivation body Γ (unary cellTail t n))) :
    Nonempty (Derivation body Γ (eqn n (rawCons h t))) := by
  obtain ⟨g⟩ := g
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  exact consEquation n h t (cellToCons n h t
    ⟨Derivation.conjunctionIntroduction g (Derivation.conjunctionIntroduction a b)⟩)

theorem zeroAccept (n : OTerm α)
    (h : Nonempty (Derivation body Γ (unary GorbowPRInternalControl.zeroTest (suc z) n))) :
    Nonempty (Derivation body Γ (eqn n z)) := by
  obtain ⟨spec⟩ := actualOriginalZeroTestGraph body α (suc z) n
  obtain ⟨branches⟩ := closedApply ⟨Derivation.conjunctionLeft spec⟩ h
  simp only [testSpec,equalEqn] at branches
  let p := eqn n z ⊓ eqn (suc z) (suc z)
  let q := (eqn n z).not ⊓ eqn (suc z) z
  have yes : Derivation body (p :: Γ) (eqn n z) :=
    Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)
  have no : Derivation body (q :: Γ) (eqn n z) :=
    Derivation.explosion (sucNeZeroApply
      (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)))
  exact ⟨disjunctionElimination branches
    (Derivation.implicationIntroduction yes) (Derivation.implicationIntroduction no)⟩

theorem packedArity (xs : List (OTerm α)) :
    Nonempty (Derivation body Γ (unary (exactBody xs.length) (suc z) (packedBody xs))) := by
  induction xs with
  | nil => exact zeroTestAtZero z ⟨refl z⟩
  | cons h xs ih =>
    let tail := packedBody xs
    let code := rawCons h tail
    obtain ⟨cell⟩ := canonicalCell (body := body) (Γ := Γ) h tail
    have step := makeUnary (exactBody xs.length) cellTail (suc z) code tail ih
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight cell)⟩
    exact conjunctionAccept cellGood (applyUnary (exactBody xs.length) cellTail) ![code]
      ⟨Derivation.conjunctionLeft cell⟩ step

theorem packedReports (root : OTerm α) (src : Program 1) (xs : List (OTerm α))
    (h : Nonempty (Derivation body Γ (unary src (packedBody xs) root))) :
    Reports body Γ root src xs := by
  induction xs generalizing src with
  | nil => trivial
  | cons x xs ih =>
    let tail := packedBody xs
    let code := rawCons x tail
    obtain ⟨cell⟩ := canonicalCell (body := body) (Γ := Γ) x tail
    refine ⟨makeUnary cellHead src x root code
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩ h, ?_⟩
    exact ih (applyUnary cellTail src) (makeUnary cellTail src tail root code
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight cell)⟩ h)

/-- Associating the two literal selector calls is a cut with their actual
graph witnesses, not the replacement of a compiled program by a native equation. -/
theorem associateTail (p src : Program 1) (o root cur : OTerm α)
    (outer : Nonempty (Derivation body Γ (unary (applyUnary p cellTail) o cur)))
    (inner : Nonempty (Derivation body Γ (unary src cur root))) :
    Nonempty (Derivation body Γ (unary (applyUnary p (applyUnary cellTail src)) o root)) := by
  apply programCases cellTail ![cur] _
  intro β j Δ t hJ actual
  rw [unaryRename]
  rw [inputsRename] at actual
  let c := cur.relabel j
  let n := root.relabel j
  let v := o.relabel j
  have a := moveReport j Δ hJ _ o cur outer
  have b := moveReport j Δ hJ _ cur root inner
  exact makeUnary p (applyUnary cellTail src) v n t
    (takeUnary p cellTail v c t a actual) (makeUnary cellTail src t n c actual b)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
