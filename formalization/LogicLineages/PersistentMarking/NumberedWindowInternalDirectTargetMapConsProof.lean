module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapConsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapCons
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRawListRecursion (recGraph)
open ID1Completion.InternalRawListRecursionProof (consForward stepCases)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue outputTransport)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectTargetMapConsTargets
open NumberedWindowInternalDirectTargetMapStep (exactOpenTargetMapStep)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (keepThrough)
open NumberedWindowInternalDirectInsertedTargetsMapTargets
open NumberedWindowInternalDirectWitnessEnvelopeTargets (guardAt)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename unaryRename)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem joinedCons (row previous projected head tail : OTerm α)
    (e : Nonempty (Derivation B Γ (eqn previous (suc tail))))
    (chosen : Nonempty (Derivation B Γ (unary (field 0) head row)))
    (run : Nonempty (Derivation B Γ (programGraph joined projected ![row,previous]))) :
    Nonempty (Derivation B Γ (consGraph projected head tail)) := by
  let xs : Fin 2 → OTerm α := ![row,previous]
  have hd : Nonempty (Derivation B Γ (programGraph (atHead (field 0)) head xs)) := by
    apply compositionValue (field 0) (Fin.cons (.projection 0) Fin.elim0) head xs ![row] chosen
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 0 xs
  have tl : Nonempty (Derivation B Γ (programGraph tailPayload tail xs)) := by
    apply compositionValue predecessor (Fin.cons (.projection 1) Fin.elim0) tail xs ![suc tail]
      (predecessorSuccessor tail)
    intro i
    obtain rfl := Fin.eq_zero i
    exact outputTransport (.projection 1) previous (suc tail) xs e (projectionValue 1 xs)
  apply compositionRecover consCode (Fin.cons (atHead (field 0)) (Fin.cons tailPayload Fin.elim0))
    projected xs (Fin.cons head (Fin.cons tail Fin.elim0)) run
  intro i
  exact Fin.cases hd (Fin.cases tl (fun j => Fin.elim0 j)) i

private theorem emptyParamsRename {α β : Type} (j : α → β) :
    (fun i : Fin 0 => ((Fin.elim0 i : OTerm α)).relabel j) = Fin.elim0 := by
  funext i
  exact Fin.elim0 i

private theorem oneTape (q : OTerm α) :
    (![q] : Fin 1 → OTerm α) = Fin.cons q Fin.elim0 := by
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

private theorem twoTape (u v : OTerm α) :
    (![u,v] : Fin 2 → OTerm α) = Fin.cons u (Fin.cons v Fin.elim0) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i

theorem exactOpenTargetMapCons : ExactOpenTargetMapCons := by
  intro B α Γ code row tail projected goal cell hit next
  have acceptedRec : Nonempty (Derivation B Γ (recGraph targetBase targetStep
      (suc projected) code Fin.elim0)) := by
    change Nonempty (Derivation B Γ (programGraph scratchTargets (suc projected)
      (Fin.cons code Fin.elim0)))
    simpa only [oneTape,unary] using hit
  have step := consForward targetBase targetStep code row tail (suc projected) Fin.elim0 cell acceptedRec
  apply stepCases targetBase targetStep (suc projected) row tail Fin.elim0 goal step
  intro β j Δ prev keep sub stepGraph
  simp only [emptyParamsRename,sucRelabel] at sub stepGraph
  have prior : Nonempty (Derivation B Δ (unary scratchTargets prev (tail.relabel j))) := by
    simpa only [oneTape,unary,recGraph,scratchTargets] using sub
  apply exactOpenTargetMapStep B β Δ (row.relabel j) prev (projected.relabel j) (goal.relabel j)
    (by simpa only [twoTape] using stepGraph)
  intro γ l Ω pt retain ep guard run
  let R := (row.relabel j).relabel l
  let U := prev.relabel l
  let P := (projected.relabel j).relabel l
  let T := (tail.relabel j).relabel l
  have mapped : Nonempty (Derivation B Ω (unary scratchTargets (suc pt) T)) := by
    have a := renameInto prior l Ω retain
    rw [unaryRename] at a
    exact outputTransport scratchTargets U (suc pt) ![T] ep a
  apply programCases (field 0) ![R] ((goal.relabel j).relabel l)
  intro δ m Ξ ht preserve fieldReport
  rw [inputsRename] at fieldReport
  have g := renameInto guard m Ξ preserve
  rw [unaryRename,sucRelabel,zRelabel] at g
  have prevMap := renameInto mapped m Ξ preserve
  rw [unaryRename,sucRelabel] at prevMap
  have eq := renameInto ep m Ξ preserve
  rw [eqnRelabel,sucRelabel] at eq
  have c := joinedCons (R.relabel m) (U.relabel m) (P.relabel m) ht (pt.relabel m)
    eq fieldReport (renamePair joined P R U run m preserve)
  let ρ := m ∘ (l ∘ j)
  rw [formulaRelabelComposition j l goal,formulaRelabelComposition (l ∘ j) m goal]
  apply next δ ρ Ξ ht (pt.relabel m) (keepThrough (l ∘ j) m (keepThrough j l keep retain) preserve)
  · simpa only [ρ,R,Term.relabel_relabel] using g
  · simpa only [ρ,R,Term.relabel_relabel,unary] using fieldReport
  · simpa only [ρ,T,Term.relabel_relabel] using prevMap
  · simpa only [ρ,P,Term.relabel_relabel] using c

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapCons
