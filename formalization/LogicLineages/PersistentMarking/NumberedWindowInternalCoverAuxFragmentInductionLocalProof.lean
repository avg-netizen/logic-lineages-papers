module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionLocalProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn bindEmbedding liftBind varBind suc z)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalClosedPrograms (allBlock)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalElimination)
open ID1Completion.InternalStrongInductionSyntaxProof (belowElimSyntax)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowSubst)
open NumberedWindowInternalCoverAuxFragmentGuardTargets (fragmentGuard)
open NumberedWindowInternalCoverAuxFragmentInductionSyntaxTargets
open NumberedWindowInternalCoverAuxFragmentInductionSyntaxProof (forwardMotiveAt forwardResultWitness)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem moveForwardWindowKey (W : Program 3) (ctx ty fromKey toKey : OTerm α)
    (equalKeys : Nonempty (Derivation body Γ (eqn fromKey toKey)))
    (actual : Nonempty (Derivation body Γ (windowAt W ctx ty fromKey))) :
    Nonempty (Derivation body Γ (windowAt W ctx ty toKey)) := by
  let θ : Formula (α ⊕ Fin 1) := windowAt W (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (.var (.inr 0))
  have instantiateKey (key : OTerm α) : instantiate θ (emb key) = windowAt W ctx ty key := by
    simp only [θ,instantiate,bindEmbedding,windowSubst,liftBind,varBind]
  obtain ⟨equalKeys⟩ := equalKeys
  obtain ⟨actual⟩ := actual
  have next := Derivation.equalityElimination θ (emb fromKey) (emb toKey) equalKeys
    (by rw [instantiateKey]; exact actual)
  rw [instantiateKey] at next
  exact ⟨next⟩

theorem selectForwardResult (P Q : Program 3) (ctx raw result : OTerm α)
    (family : Nonempty (Derivation body Γ (allBlock (forwardMatrix P Q ctx raw))))
    (actual : Nonempty (Derivation body Γ (windowAt P ctx result raw))) :
    Nonempty (Derivation body Γ (windowAt Q ctx result raw)) := by
  have specialized := actualFiniteUniversalElimination body α 1 Γ (forwardMatrix P Q ctx raw)
    (fun _ : Fin 1 => emb result) family
  rw [forwardResultWitness] at specialized
  obtain ⟨forward⟩ := specialized
  obtain ⟨actual⟩ := actual
  exact ⟨Derivation.implicationElimination forward actual⟩

theorem actualBelowChildForward (P Q : Program 3) (ctx raw child result : OTerm α)
    (earlier : Nonempty (Derivation body Γ (forwardBelow P Q ctx raw)))
    (bound : Nonempty (Derivation body Γ (ltF child raw)))
    (accepted : Nonempty (Derivation body Γ (unary fragmentGuard (suc z) child)))
    (before : Nonempty (Derivation body Γ (windowAt P ctx result child))) :
    Nonempty (Derivation body Γ (windowAt Q ctx result child)) := by
  obtain ⟨earlier⟩ := earlier
  obtain ⟨bound⟩ := bound
  obtain ⟨accepted⟩ := accepted
  have atChild := Derivation.universalElimination (emb child) earlier
  rw [belowElimSyntax,forwardMotiveAt] at atChild
  have guardImplication := Derivation.implicationElimination atChild bound
  have family := Derivation.implicationElimination guardImplication accepted
  exact selectForwardResult P Q ctx child result ⟨family⟩ before

#print axioms moveForwardWindowKey
#print axioms selectForwardResult
#print axioms actualBelowChildForward

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionLocalProof
