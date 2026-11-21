module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterOpenRowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterOpenChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalRawListRecursionProof (consForward stepCases)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseDirectedFilter
open NumberedWindowInternalSparseDirectedFilterTargets
open NumberedWindowInternalSparseDirectedFilterOpenSyntaxProof
  (reportRename reportUnfold reportInstance)
open NumberedWindowInternalSparseDirectedFilterOpenRowProof (rowCases)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Expose only the actual result of the same pass on this genuine tail.
Both row alternatives share it under a single original existential. -/
private theorem decompose (E : Program 4) (vertices h tail seen ctx ty out : OTerm α)
    (input : Nonempty (Derivation body Γ (cell vertices h tail)))
    (run : Nonempty (Derivation body Γ (passGraph E out vertices seen ctx ty))) :
    Nonempty (Derivation body Γ (restReport E out h tail seen ctx ty)) := by
  have step := consForward (constantZero 3) (filterStep E) vertices h tail out
    (![seen,ctx,ty] : Fin 3 → OTerm α) input run
  apply stepCases (constantZero 3) (filterStep E) out h tail
    (![seen,ctx,ty] : Fin 3 → OTerm α) (restReport E out h tail seen ctx ty) step
  intro β j Δ rest _ tailRun rowRun
  rw [tripleInputsRename] at tailRun rowRun
  rw [reportRename]
  obtain ⟨alternatives⟩ := rowCases E (out.relabel j) (h.relabel j) rest
    (seen.relabel j) (ctx.relabel j) (ty.relabel j) rowRun
  obtain ⟨realTail⟩ := tailRun
  rw [reportUnfold]
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb rest)
  rw [reportInstance]
  exact Derivation.conjunctionIntroduction realTail alternatives

theorem exact_OpenDirectedFilterCons : ExactOpenDirectedFilterCons := by
  intro E body α Γ vertices h tail seen ctx ty out
  let prem := cell vertices h tail ⊓ passGraph E out vertices seen ctx ty
  have it : Derivation body (prem :: Γ) prem := Derivation.hypothesis List.mem_cons_self
  obtain ⟨result⟩ := decompose (body := body) (Γ := prem :: Γ)
    E vertices h tail seen ctx ty out
    ⟨Derivation.conjunctionLeft it⟩ ⟨Derivation.conjunctionRight it⟩
  exact ⟨Derivation.implicationIntroduction result⟩

#print axioms exact_OpenDirectedFilterCons
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterOpenChecks
