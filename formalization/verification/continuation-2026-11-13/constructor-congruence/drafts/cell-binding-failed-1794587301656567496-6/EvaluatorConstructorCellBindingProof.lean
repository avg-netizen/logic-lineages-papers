module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCongruenceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCellBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryDeletionRowsCongruence
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Introduce actual internal all-position agreement from a proof of each
arbitrary in-range cell. The constructor induction supplies this callback;
CellAgreement itself is not assumed. -/
theorem introduction (Q : Program 2) (count left right parameter : OTerm alpha)
 (cell : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (index a b : OTerm beta),
   (∀ q ∈ Delta, q.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (OriginalContextInsertion.Below index (count.relabel j))) →
   Nonempty (Derivation body Theta (graph3 (OriginalHereditaryDeletionRows.observation Q) a index (left.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (graph3 (OriginalHereditaryDeletionRows.observation Q) b index (right.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (equal a b))) :
 Nonempty (Derivation body Delta (CellAgreement Q count left parameter right parameter)) := by
 apply InternalClosedProgramsBindingProof.introduction body alpha 3 Delta
 let phi := cellFields Q (count.relabel Sum.inl) (left.relabel Sum.inl) (parameter.relabel Sum.inl)
   (right.relabel Sum.inl) (parameter.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
 let Theta := phi :: Delta.map (fun q => q.relabel Sum.inl)
 have hh : Nonempty (Derivation body Theta phi) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have he := cell (alpha ⊕ Fin 3) Sum.inl Theta (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
   (fun q hq => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
   (andLeft hh) (andLeft (andRight hh)) (andRight (andRight hh))
 exact ⟨Derivation.implicationIntroduction (Classical.choice he)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCellBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCellBindingProof
