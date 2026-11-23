module

public import LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastObjectProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue outputTransport programRename)
open ID1Completion.InternalEqualityTest (predecessor equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalRankCheckedLeast
open NumberedWindowInternalRankCheckedLeastReportsProof (exact_OpenRankCheckedLeastReports)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem onTape (g : Program 1) (p : Program 3)
    (xs : Fin 3 → OTerm α) (k m : OTerm α)
    (call : Nonempty (Derivation B Γ (unary g m k)))
    (input : Nonempty (Derivation B Γ (programGraph p k xs))) :
    Nonempty (Derivation B Γ (programGraph (unaryOn g p) m xs)) := by
  apply compositionValue g (fun _ : Fin 1 => p) m xs ![k] call
  intro i
  obtain rfl := Fin.eq_zero i
  exact input

private theorem matchOutput (g : Program 1) (L : Program 3)
    (ctx ty seed k m n : OTerm α)
    (old : Nonempty (Derivation B Γ (programGraph L (suc k) ![ctx,ty,seed])))
    (test : Nonempty (Derivation B Γ (programGraph (rankEq g L) (suc z) ![ctx,ty,seed])))
    (seedCall : Nonempty (Derivation B Γ (unary g m seed)))
    (outCall : Nonempty (Derivation B Γ (unary g n k))) :
    Nonempty (Derivation B Γ (unary g m k)) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,seed]
  have s : Nonempty (Derivation B Γ (programGraph (seedRank g) m xs)) :=
    onTape g (.projection 2) xs seed m seedCall (projectionValue 2 xs)
  have pred := onTape predecessor L xs (suc k) k (predecessorSuccessor k) old
  have o : Nonempty (Derivation B Γ (programGraph (outputRank g L) n xs)) :=
    onTape g (unaryOn predecessor L) xs k n outCall pred
  have equalRank := compositionRecover equalityTest
    (Fin.cons (seedRank g) (Fin.cons (outputRank g L) Fin.elim0)) (suc z) xs
    (Fin.cons m (Fin.cons n Fin.elim0)) test (fun i => Fin.cases s
      (fun t => Fin.cases o (fun h => Fin.elim0 h) t) i)
  obtain ⟨e⟩ := equalityOfAcceptance m n equalRank
  exact outputTransport g n m ![k] ⟨symm e⟩ outCall

/-- The least's actual k is unchanged. Its real g graph has the exact
same output m as the held original raw seed graph, including zero. -/
theorem exact_OpenRankCheckedLeastConservation (g : Program 1) (L : Program 3)
    (ctx ty seed k m : OTerm α)
    (checked : Nonempty (Derivation B Γ (programGraph (checkedLeast g L) (suc k) ![ctx,ty,seed])))
    (seedCall : Nonempty (Derivation B Γ (unary g m seed))) :
    Nonempty (Derivation B Γ (programGraph L (suc k) ![ctx,ty,seed])) ∧
    Nonempty (Derivation B Γ (unary g m k)) := by
  obtain ⟨pair⟩ := exact_OpenRankCheckedLeastReports g L ctx ty seed k checked
  have old : Nonempty (Derivation B Γ (programGraph L (suc k) ![ctx,ty,seed])) :=
    ⟨Derivation.conjunctionLeft pair⟩
  have test : Nonempty (Derivation B Γ (programGraph (rankEq g L) (suc z) ![ctx,ty,seed])) :=
    ⟨Derivation.conjunctionRight pair⟩
  refine ⟨old,?_⟩
  apply programCases g (![k] : Fin 1 → OTerm α) (unary g m k)
  intro β j Δ n keep actual
  rw [unaryInputsRename] at actual
  rw [unaryRename]
  have o := renameInto old j Δ keep
  have t := renameInto test j Δ keep
  have s := renameInto seedCall j Δ keep
  simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at o t
  rw [unaryRename] at s
  exact matchOutput g L (ctx.relabel j) (ty.relabel j) (seed.relabel j) (k.relabel j)
    (m.relabel j) n o t s actual

#print axioms exact_OpenRankCheckedLeastConservation
end LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastObjectProof
