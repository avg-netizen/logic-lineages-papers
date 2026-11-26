module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScan
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators (Positive)
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue outputTransport valueUnique programRename)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalRawListRecursion (listRec recGraph)
open ID1Completion.InternalRawListRecursionProof (nilValue consForward stepCases)
open ID1Completion.InternalRawListRecursionSyntaxProof (recRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalListCodec (consCode)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open NumberedWindowInternalDirectInsertedScanTargets
open NumberedWindowInternalDirectInsertedRowTargets
  (liftLeft insertedRow parseRemoved poolReady poolCode oneTerm Zero)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem poolReport (inserted removed decoded : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation B Γ (unary parser (OrdinaryArithmetic.succTerm decoded) inserted))) :
    Nonempty (Derivation B Γ (programGraph poolCode decoded ![inserted,removed])) := by
  let xs : Fin 2 → OrdinaryArithmetic.Term α := ![inserted,removed]
  have carried : Nonempty (Derivation B Γ (programGraph parseRemoved
      (OrdinaryArithmetic.succTerm decoded) xs)) := by
    apply compositionValue parser ![.projection 0] (OrdinaryArithmetic.succTerm decoded) xs ![inserted] h
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 0 xs
  apply compositionValue predecessor ![parseRemoved] decoded xs ![OrdinaryArithmetic.succTerm decoded]
  · exact predecessorSuccessor decoded
  · intro i
    obtain rfl := Fin.eq_zero i
    exact carried

theorem exactOpenScanParser : ExactOpenScanParser := by
  intro r B α Γ inserted removed decoded pool accepted
  let xs : Fin 2 → OrdinaryArithmetic.Term α := ![inserted,removed]
  obtain ⟨parts⟩ := conjunctionRecover poolReady (scanAt r) xs accepted
  apply compositionRecover (scanLoop r) ![poolCode,.projection 1] oneTerm xs
    (Fin.cons decoded ![removed]) ⟨Derivation.conjunctionRight parts⟩
  intro i
  exact Fin.cases (poolReport inserted removed decoded pool)
    (Fin.cases (projectionValue 1 xs) (fun noIndex => Fin.elim0 noIndex)) i

theorem exactOpenScanNil : ExactOpenScanNil := by
  intro r B α Γ removed
  exact nilValue scanBase (scanStep r) oneTerm ![removed] (literalGraph 1 ![removed])

private theorem stepHead (r : Program 3) (row prior removed : OrdinaryArithmetic.Term α)
    (hit : Nonempty (Derivation B Γ (programGraph (rowAt r) oneTerm
      (Fin.cons row (Fin.cons prior ![removed]))))) :
    Nonempty (Derivation B Γ (rowAccept r row removed)) := by
  let xs : Fin 3 → OrdinaryArithmetic.Term α := Fin.cons row (Fin.cons prior ![removed])
  apply compositionRecover (insertedRow r) ![.projection 2,.projection 0] oneTerm xs
    ![removed,row] hit
  intro i
  exact Fin.cases (projectionValue 2 xs)
    (Fin.cases (projectionValue 0 xs) (fun noIndex => Fin.elim0 noIndex)) i

private theorem peelAcceptedStep (r : Program 3)
    (row prior tail removed : OrdinaryArithmetic.Term α)
    (tailGraph : Nonempty (Derivation B Γ (recGraph scanBase (scanStep r) prior tail ![removed])))
    (hit : Nonempty (Derivation B Γ (programGraph (scanStep r) oneTerm
      (Fin.cons row (Fin.cons prior ![removed]))))) :
    Nonempty (Derivation B Γ (rowAccept r row removed ⊓ loopAccept r tail removed)) := by
  let xs : Fin 3 → OrdinaryArithmetic.Term α := Fin.cons row (Fin.cons prior ![removed])
  obtain ⟨parts⟩ := conjunctionRecover (rowAt r) (.projection 1) xs hit
  obtain ⟨head⟩ := stepHead r row prior removed ⟨Derivation.conjunctionLeft parts⟩
  have eq := valueUnique (.projection 1) prior oneTerm xs
    (projectionValue 1 xs) ⟨Derivation.conjunctionRight parts⟩
  obtain ⟨now⟩ := outputTransport (scanLoop r) prior oneTerm (Fin.cons tail ![removed]) eq tailGraph
  exact ⟨Derivation.conjunctionIntroduction head now⟩

private theorem unaryTape {α β : Type} (a : OrdinaryArithmetic.Term α) (j : α → β) :
    (fun (i : Fin 1) => ((![a] : Fin 1 → OrdinaryArithmetic.Term α) i).relabel j) =
      ![a.relabel j] := by
  funext i
  exact Fin.cases rfl (fun k => Fin.elim0 k) i

private theorem binaryTape {α β : Type} (a b : OrdinaryArithmetic.Term α) (j : α → β) :
    (fun (i : Fin 2) => ((![a,b] : Fin 2 → OrdinaryArithmetic.Term α) i).relabel j) =
      ![a.relabel j,b.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i

private theorem acceptsRename {α β : Type} (r : Program 3) (row tail removed : OrdinaryArithmetic.Term α)
    (j : α → β) :
    (rowAccept r row removed ⊓ loopAccept r tail removed).relabel j =
      (rowAccept r (row.relabel j) (removed.relabel j) ⊓
        loopAccept r (tail.relabel j) (removed.relabel j)) := by
  simp only [conjunctionRename,rowAccept,loopAccept,programRename,recRename,unaryTape,binaryTape,
    oneTerm,sucRelabel,zRelabel]

theorem exactOpenScanCons : ExactOpenScanCons := by
  intro r B α Γ code row tail removed cons hit
  let target := rowAccept r row removed ⊓ loopAccept r tail removed
  have openStep := consForward scanBase (scanStep r) code row tail oneTerm ![removed] cons hit
  apply stepCases scanBase (scanStep r) oneTerm row tail ![removed] target openStep
  intro β j Δ prior _ tailGraph stepGraph
  rw [show target.relabel j =
    rowAccept r (row.relabel j) (removed.relabel j) ⊓
      loopAccept r (tail.relabel j) (removed.relabel j) from acceptsRename _ _ _ _ j]
  simp only [unaryTape] at tailGraph
  simp only [unaryTape,oneTerm,sucRelabel,zRelabel] at stepGraph
  exact peelAcceptedStep r (row.relabel j) prior (tail.relabel j) (removed.relabel j)
    tailGraph stepGraph

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScan
