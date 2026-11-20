module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationHeadRowsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationHeadInductionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding nextEmbedding liftBind varBind)
open ID1Completion.InternalTagArithmeticSupportProof (natInduction)
open ID1Completion.InternalAdditionLawsProof (liftNext varNext)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph stepGraph)
open NumberedWindowInternalSparsePositiveIterationHeadSyntaxProof
open NumberedWindowInternalSparsePositiveIterationHeadRowsProof (baseRow nextRow)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Actual object-language induction over the arbitrary arithmetic fuel.
The invariant universally compares both genuine loop outputs. -/
theorem allFuel (raw : Program 5) (least : Program 3) (p : Plan α) (fuel old new : OTerm α)
    (before : Nonempty (Derivation body Γ (scratchGraph old p.originalCertificate p.originalCurrent)))
    (after : Nonempty (Derivation body Γ (scratchGraph new p.nextCertificate p.nextCurrent)))
    (stepRel : Nonempty (Derivation body Γ
      (stepGraph raw least new z old p.context p.ty p.originalCurrent p.originalCertificate))) :
    Nonempty (Derivation body Γ (sameAt raw least fuel p)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let lifted := p.map (fun t => t.relabel j)
  let theta := sameAt raw least v lifted
  have base : Derivation body Γ (instantiate theta (emb z)) := by
    simp only [theta,lifted,j,v,instantiate,bindEmbedding,sameAtSubst,Plan.map,liftBind,varBind]
    exact Classical.choice (baseRow raw least p old new before after stepRel)
  let Δ := theta :: Γ.map weaken
  have next := nextRow (body := body) (Γ := Δ) raw least lifted v
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have step : Derivation body (theta :: Γ.map weaken) (successorInstance theta) := by
    simp only [theta,lifted,j,v,successorInstance,nextEmbedding,sameAtSubst,Plan.map,liftNext,varNext]
    exact Classical.choice next
  have result := Derivation.universalElimination (emb fuel) (natInduction theta base step)
  simpa only [theta,lifted,j,v,instantiate,bindEmbedding,sameAtSubst,Plan.map,liftBind,varBind]
    using (Nonempty.intro result)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationHeadInductionProof
