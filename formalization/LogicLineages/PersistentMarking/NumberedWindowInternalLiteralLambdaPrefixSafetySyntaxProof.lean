module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixScopeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunSuccessProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixSafetySyntaxProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn eqnRelabel eqnSubst zRelabel sucRelabel zSubst sucSubst)
open ID1Completion.InternalTagArithmeticSupportProof (symm trans)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (stateRename stateSubst)
open NumberedWindowInternalSparseRawRunSuccessProof (headRead)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)

abbrev rejectedState {α : Type} : OTerm α := stateTerm z z

def prefixSafe {α : Type} (v : OTerm α) : Formula α :=
  unary cellHead (suc z) v ⊔ eqn v rejectedState

private theorem unaryInputsSubst {α β : Type} (v : OTerm α) (ts : α → OTerm β) :
    (fun i : Fin 1 => ((![v] : Fin 1 → OTerm α) i).subst ts) = ![v.subst ts] := by
  funext i
  obtain rfl := Fin.eq_zero i
  rfl

theorem prefixSafeRename {α β : Type} (v : OTerm α) (j : α → β) :
    (prefixSafe v).relabel j = prefixSafe (v.relabel j) := by
  change (unary cellHead (suc z) v).relabel j ⊔ (eqn v rejectedState).relabel j = _
  rw [unaryRename,eqnRelabel,sucRelabel,zRelabel,stateRename,zRelabel]
  rfl

theorem prefixSafeSubst {α β : Type} (v : OTerm α) (ts : α → OTerm β) :
    (prefixSafe v).subst (fun a => emb (ts a)) = prefixSafe (v.subst ts) := by
  change (programGraph cellHead (suc z) ![v]).subst (fun a => emb (ts a)) ⊔
    (eqn v rejectedState).subst (fun a => emb (ts a)) = _
  rw [programSubst,unaryInputsSubst,eqnSubst,sucSubst,zSubst,stateSubst,zSubst]
  rfl

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem oneStateSafe (v : OTerm α)
    (one : D B Γ (unary cellHead (suc z) v)) : D B Γ (prefixSafe v) :=
  one.map orLeft

theorem rejectedStateSafe (v : OTerm α) (rejected : D B Γ (eqn v rejectedState)) :
    D B Γ (prefixSafe v) := rejected.map orRight

theorem prefixSafeMove (v out : OTerm α) (safe : D B Γ (prefixSafe v)) (same : D B Γ (eqn v out)) :
    D B Γ (prefixSafe out) := by
  obtain ⟨e⟩ := same
  obtain ⟨s⟩ := safe
  let P := unary cellHead (suc z) v
  let R := eqn v rejectedState
  have left : Derivation B (P :: Γ) (prefixSafe out) := Classical.choice
    (oneStateSafe out (headTransport cellHead (suc z) v out Fin.elim0 ⟨addHyp e P⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩))
  have right : Derivation B (R :: Γ) (prefixSafe out) := Classical.choice
    (rejectedStateSafe out ⟨trans (symm (addHyp e R)) (Derivation.hypothesis List.mem_cons_self)⟩)
  exact ⟨disjunctionElimination s (Derivation.implicationIntroduction left) (Derivation.implicationIntroduction right)⟩

#print axioms prefixSafeRename
#print axioms prefixSafeSubst
#print axioms prefixSafeMove
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixSafetySyntaxProof
