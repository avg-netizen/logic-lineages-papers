module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenBodyProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (outputTransport)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelope
open NumberedWindowInternalSparsePathEnvelopeTargets
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof

/-- Assemble the actual ordered body from all real selector graphs inside
the calculus. The induction is external on the finite requested arity and
is generalized over the arbitrary free-variable context at each graph cut. -/
theorem readPackedBody (body : Positive (Fin 1)) (arity : Nat) :
    ∀ (α : Type) (Γ : List (Formula α)) (root : OTerm α) (src : Program 1)
          (xs : List (OTerm α)),
      xs.length = arity →
      Nonempty (Derivation body Γ (unary (applyUnary (exactBody arity) src) (suc z) root)) →
      Reports body Γ root src xs →
      Nonempty (Derivation body Γ (unary src (packedBody xs) root)) := by
  induction arity with
  | zero =>
    intro α Γ root src xs length guard _
    cases xs with
    | cons h xs => simp at length
    | nil =>
      apply programCases src ![root] _
      intro β j Δ cur hJ here
      rw [unaryRename]
      rw [inputsRename] at here
      simp only [packedBody,zRelabel]
      have moved := moveReport j Δ hJ _ (suc z) root guard
      simp only [sucRelabel,zRelabel] at moved
      let n := root.relabel j
      have atCursor := takeUnary GorbowPRInternalControl.zeroTest src (suc z) n cur moved here
      exact outputTransport src cur z ![n] (zeroAccept cur atCursor) here
  | succ k ih =>
    intro α Γ root src xs length guard reports
    cases xs with
    | nil => simp at length
    | cons head xs =>
      have size : xs.length = k := Nat.succ.inj length
      apply programCases src ![root] _
      intro β j Δ cur hJ here
      rw [unaryRename,packedBodyRename]
      rw [inputsRename] at here
      let root' := root.relabel j
      let head' := head.relabel j
      let xs' := xs.map (fun t => t.relabel j)
      have reports' : Reports body Δ root' src (head'::xs') :=
        moveReports j Δ hJ root src (head::xs) reports
      have moved := moveReport j Δ hJ _ (suc z) root guard
      simp only [sucRelabel,zRelabel] at moved
      have atCursor := takeUnary (exactBody (k+1)) src (suc z) root' cur moved here
      obtain ⟨both⟩ := conjunctionRecover cellGood (applyUnary (exactBody k) cellTail) ![cur] atCursor
      have nextGuard := associateTail (exactBody k) src (suc z) root' cur
        ⟨Derivation.conjunctionRight both⟩ here
      have nextLength : xs'.length = k := by simpa only [xs',List.length_map] using size
      let tail := packedBody xs'
      have tailReport : Nonempty (Derivation body Δ (unary (applyUnary cellTail src) tail root')) :=
        ih β Δ root' (applyUnary cellTail src) xs' nextLength nextGuard reports'.2
      have hHead := takeUnary cellHead src head' root' cur reports'.1 here
      have hTail := takeUnary cellTail src tail root' cur tailReport here
      exact outputTransport src cur (rawCons head' tail) ![root']
        (cellEquation cur head' tail ⟨Derivation.conjunctionLeft both⟩ hHead hTail) here

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenBodyProof
