module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSliceInductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionSmallIndexProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof (zeroSuccessorCases)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof
open InternalSquareRootArithmeticSupportProof (orderLeft)
open InternalPositiveUnfoldingSupportProof
open InternalSliceInductionSyntaxProof (eqnRename)
open OriginalContextInsertionBelowCoreProof (successorStrict)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem belowOneZero (index : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (ltF index (suc z)))) :
 Nonempty (Derivation body Delta (eqn index z)) := by
 apply zeroSuccessorCases Delta index (eqn index z)
 · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
 · intro beta rho Theta pred hrho he
   have hb' := renameInto hb rho Theta hrho
   simp only [orderRename,sucRelabel,zRelabel] at hb'
   obtain ⟨he⟩ := he
   obtain ⟨hb'⟩ := hb'
   have hbad := successorStrict pred z ⟨orderLeft (suc z) he hb'⟩
   obtain ⟨hbad⟩ := hbad
   obtain ⟨hn⟩ := InternalLeastNumberProof.actualNothingBelowZero body beta pred
   exact ⟨Derivation.explosion (Derivation.implicationElimination (weakenClosed hn _) hbad)⟩

/-- Internal bounded choice for the two genuine positions in a binary row. -/
theorem belowTwoCases (index : OTerm alpha) (psi : Formula alpha)
 (hb : Nonempty (Derivation body Delta (ltF index (suc (suc z)))))
 (zero : ∀ (Theta : List (Formula alpha)), (∀ f ∈ Delta, f ∈ Theta) →
   Nonempty (Derivation body Theta (eqn index z)) → Nonempty (Derivation body Theta psi))
 (one : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta)),
   (∀ f ∈ Delta, f.relabel rho ∈ Theta) →
   Nonempty (Derivation body Theta (eqn (index.relabel rho) (suc z))) →
   Nonempty (Derivation body Theta (psi.relabel rho))) :
 Nonempty (Derivation body Delta psi) := by
 apply zeroSuccessorCases Delta index psi
 · exact zero (eqn index z :: Delta) (fun f hf => List.mem_cons_of_mem _ hf)
     ⟨Derivation.hypothesis List.mem_cons_self⟩
 · intro beta rho Theta pred hrho he
   have hb' := renameInto hb rho Theta hrho
   simp only [orderRename,sucRelabel,zRelabel] at hb'
   obtain ⟨he⟩ := he
   obtain ⟨hb'⟩ := hb'
   obtain ⟨hp⟩ := belowOneZero pred (successorStrict pred (suc z) ⟨orderLeft (suc (suc z)) he hb'⟩)
   exact one beta rho Theta hrho ⟨trans he (congSuc hp)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionSmallIndexProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionSmallIndexProof
