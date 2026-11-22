module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOwnEarlierTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOwnEarlierSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverOwnEarlierLocalProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open SourceComputabilityFormulaSupportProof (allOne)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open ID1Completion.InternalStrongInductionSyntaxProof (belowElimSyntax)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalElimination)
open NumberedWindowInternalCoverLambdaDerivedOwnTargets (lambdaLocalIH lambdaOwnClause)
open NumberedWindowInternalCoverOwnEarlierTargets
open NumberedWindowInternalCoverOwnEarlierSyntaxProof (ownAllRename ownMotiveAt ownWitness)

theorem exact_OpenCoverOwnEarlierLocalIH : ExactOpenCoverOwnEarlierLocalIH := by
  intro V W C s body α Γ ctx ty child parent hb bound valid
  obtain ⟨hb⟩ := hb
  obtain ⟨bound⟩ := bound
  obtain ⟨valid⟩ := valid
  have earlier := Derivation.universalElimination (emb child) hb
  rw [belowElimSyntax,ownMotiveAt] at earlier
  have property := Derivation.implicationElimination earlier bound
  have allData := Derivation.implicationElimination property valid
  let j : α → α ⊕ Fin 1 := Sum.inl
  let Δ : List (Formula (α ⊕ Fin 1)) := Γ.map weaken
  let out : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  have keep : ∀ f ∈ Γ, f.relabel j ∈ Δ := by
    intro f h
    exact List.mem_map.mpr ⟨f,h,rfl⟩
  have family := renameInto ⟨allData⟩ j Δ keep
  rw [ownAllRename] at family
  have atOut := actualFiniteUniversalElimination body (α ⊕ Fin 1) 3 Δ
    (ownMatrix W C s (child.relabel j)) (fun i => emb (![ctx.relabel j,ty.relabel j,out] i)) family
  rw [ownWitness] at atOut
  obtain ⟨atOut⟩ := atOut
  exact ⟨Derivation.universalIntroduction atOut⟩

#print axioms exact_OpenCoverOwnEarlierLocalIH

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverOwnEarlierLocalProof
