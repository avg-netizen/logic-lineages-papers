module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowCasesTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowCases
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators (Positive)
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAcceptance (constantZero conjunction)
open ID1Completion.InternalAcceptanceSupportProof (programCases programCompositionCases compositionRecover)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover constantZeroValue)
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue zeroSuccessorCases programRename outputTransport valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open NumberedWindowInternalDirectInsertedRowTargets
open NumberedWindowInternalDirectInsertedRow (exactOpenInsertedRow)
open NumberedWindowInternalDirectInsertedRowCasesTargets
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename inputsRename)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem binaryRename {β : Type} (a b : OrdinaryArithmetic.Term α) (j : α → β) :
    (fun i : Fin 2 => ((![a,b] : Fin 2 → OrdinaryArithmetic.Term α) i).relabel j) =
      ![a.relabel j,b.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun n => Fin.elim0 n)) i

private theorem keepThrough {β γ : Type} {Δ : List (Formula β)} {Ω : List (Formula γ)}
    (j : α → β) (k : β → γ)
    (h : ∀ p ∈ Γ, p.relabel j ∈ Δ) (g : ∀ p ∈ Δ, p.relabel k ∈ Ω) :
    ∀ p ∈ Γ, p.relabel (k ∘ j) ∈ Ω := by
  intro p hp
  rw [← formulaRelabelComposition j k p]
  exact g _ (h p hp)

private theorem readyHit (r : Program 3) (removed row : OrdinaryArithmetic.Term α)
    (hit : Nonempty (Derivation B Γ (programGraph (insertedRow r) oneTerm ![removed,row]))) :
    Nonempty (Derivation B Γ (programGraph poolReady oneTerm ![removed,row])) := by
  let xs : Fin 2 → OrdinaryArithmetic.Term α := ![removed,row]
  let inner := conjunction memberAt (positiveAt r)
  obtain ⟨h⟩ := conjunctionRecover rowGuard (conjunction poolReady inner) xs hit
  obtain ⟨q⟩ := conjunctionRecover poolReady inner xs ⟨Derivation.conjunctionRight h⟩
  exact ⟨Derivation.conjunctionLeft q⟩

private theorem positiveHit (r : Program 3) (removed row : OrdinaryArithmetic.Term α)
    (hit : Nonempty (Derivation B Γ (programGraph (insertedRow r) oneTerm ![removed,row]))) :
    Nonempty (Derivation B Γ (programGraph (positiveAt r) oneTerm ![removed,row])) := by
  let xs : Fin 2 → OrdinaryArithmetic.Term α := ![removed,row]
  let p := positiveAt r
  let inner := conjunction memberAt p
  obtain ⟨h⟩ := conjunctionRecover rowGuard (conjunction poolReady inner) xs hit
  obtain ⟨q⟩ := conjunctionRecover poolReady inner xs ⟨Derivation.conjunctionRight h⟩
  obtain ⟨v⟩ := conjunctionRecover memberAt p xs ⟨Derivation.conjunctionRight q⟩
  exact ⟨Derivation.conjunctionRight v⟩

private theorem parserZeroContradiction (removed row : OrdinaryArithmetic.Term α)
    (parsed : Nonempty (Derivation B Γ (unary parser z removed)))
    (ready : Nonempty (Derivation B Γ (programGraph poolReady oneTerm ![removed,row]))) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  let xs : Fin 2 → OrdinaryArithmetic.Term α := ![removed,row]
  have h : Nonempty (Derivation B Γ (programGraph parseRemoved z xs)) := by
    apply compositionValue parser ![.projection 0] z xs ![removed] parsed
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 0 xs
  have zero := zeroBranchElim parseRemoved (constantZero 2) (literal 2 1)
    oneTerm xs h ready
  obtain ⟨bad⟩ := valueUnique (constantZero 2) oneTerm z xs zero (constantZeroValue xs)
  exact ⟨sucNeZeroApply bad⟩

private theorem parserCases (removed row : OrdinaryArithmetic.Term α) (goal : Formula α)
    (ready : Nonempty (Derivation B Γ (programGraph poolReady oneTerm ![removed,row])))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (decoded : OrdinaryArithmetic.Term β),
      (∀ q ∈ Γ, q.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (unary parser (suc decoded) (removed.relabel j))) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply programCases parser ![removed] goal
  intro β j Δ out keep report
  rw [inputsRename] at report
  have hr : Nonempty (Derivation B Δ
      (programGraph poolReady oneTerm ![removed.relabel j,row.relabel j])) := by
    simpa only [programRename,binaryRename,oneTerm,sucRelabel,zRelabel] using renameInto ready j Δ keep
  apply zeroSuccessorCases Δ out (goal.relabel j)
  · let E := eqn out z
    obtain ⟨present⟩ := report
    obtain ⟨guarded⟩ := hr
    have e : Nonempty (Derivation B (E :: Δ) E) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have zero := outputTransport parser out z ![removed.relabel j] e ⟨addHyp present E⟩
    obtain ⟨bad⟩ := parserZeroContradiction (removed.relabel j) (row.relabel j) zero
      ⟨addHyp guarded E⟩
    exact ⟨Derivation.explosion bad⟩
  · intro γ k Ω decoded retain e
    have held := renameInto report k Ω retain
    simp only [programRename,inputsRename,Term.relabel_relabel] at held
    have success := outputTransport parser (out.relabel k) (suc decoded) ![removed.relabel (k ∘ j)] e held
    rw [formulaRelabelComposition]
    exact next γ (k ∘ j) Ω decoded (keepThrough j k keep retain) success

private theorem fromRightField (n : Nat) (removed row out : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation B Γ (programGraph (rowField n) out ![removed,row]))) :
    Nonempty (Derivation B Γ (unary (field n) out row)) := by
  apply compositionRecover (field n) ![.projection 1] out ![removed,row] ![row] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 1 ![removed,row]

theorem exactOpenInsertedRowCases : ExactOpenInsertedRowCases := by
  intro r B α Γ removed row goal hit next
  apply parserCases removed row goal (readyHit r removed row hit)
  intro β j Δ decoded keep parsed
  let R := removed.relabel j
  let A := row.relabel j
  let xs : Fin 2 → OrdinaryArithmetic.Term β := ![R,A]
  have saved : Nonempty (Derivation B Δ (programGraph (insertedRow r) oneTerm xs)) := by
    simpa only [R,A,xs,programRename,binaryRename,oneTerm,sucRelabel,zRelabel] using renameInto hit j Δ keep
  have cut := positiveHit r R A saved
  apply programCompositionCases r ![rowField 1,rowField 2,rowField 0] oneTerm xs (goal.relabel j) cut
  intro γ k values Ω retain _ fields
  let ρ := k ∘ j
  let t := values 2
  let d := values 0
  let w := values 1
  have saved' : Nonempty (Derivation B Ω (programGraph (insertedRow r) oneTerm
      ![removed.relabel ρ,row.relabel ρ])) := by
    simpa only [ρ,R,A,xs,programRename,binaryRename,oneTerm,sucRelabel,zRelabel,
      Term.relabel_relabel] using renameInto saved k Ω retain
  have parsed' : Nonempty (Derivation B Ω (unary parser (suc (decoded.relabel k)) (removed.relabel ρ))) := by
    simpa only [ρ,unaryRename,sucRelabel,Term.relabel_relabel] using renameInto parsed k Ω retain
  have a0 : Nonempty (Derivation B Ω (programGraph (rowField 0) t
      ![removed.relabel ρ,row.relabel ρ])) := by
    have read := fields (2 : Fin 3)
    change Nonempty (Derivation B Ω (programGraph (rowField 0) t
      (fun a : Fin 2 => (xs a).relabel k))) at read
    simpa only [ρ,R,A,xs,binaryRename,Term.relabel_relabel] using read
  have a1 : Nonempty (Derivation B Ω (programGraph (rowField 1) d
      ![removed.relabel ρ,row.relabel ρ])) := by
    have read := fields (0 : Fin 3)
    change Nonempty (Derivation B Ω (programGraph (rowField 1) d
      (fun a : Fin 2 => (xs a).relabel k))) at read
    simpa only [ρ,R,A,xs,binaryRename,Term.relabel_relabel] using read
  have a2 : Nonempty (Derivation B Ω (programGraph (rowField 2) w
      ![removed.relabel ρ,row.relabel ρ])) := by
    have read := fields (1 : Fin 3)
    change Nonempty (Derivation B Ω (programGraph (rowField 2) w
      (fun a : Fin 2 => (xs a).relabel k))) at read
    simpa only [ρ,R,A,xs,binaryRename,Term.relabel_relabel] using read
  have f0 := fromRightField 0 (removed.relabel ρ) (row.relabel ρ) t a0
  have f1 := fromRightField 1 (removed.relabel ρ) (row.relabel ρ) d a1
  have f2 := fromRightField 2 (removed.relabel ρ) (row.relabel ρ) w a2
  have packed := exactOpenInsertedRow r B γ Ω (removed.relabel ρ) (row.relabel ρ)
    (decoded.relabel k) t d w parsed' f0 f1 f2 saved'
  rw [formulaRelabelComposition]
  exact next γ ρ Ω (decoded.relabel k) t d w (keepThrough j k keep retain)
    ⟨parsed',f0,f1,f2,packed⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowCases
