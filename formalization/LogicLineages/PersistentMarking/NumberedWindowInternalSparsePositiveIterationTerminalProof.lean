module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationBindingProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationTerminalProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb bindEmbedding nextEmbedding liftBind varBind zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (natInduction addZero addSucc symm)
open ID1Completion.InternalAdditionLawsProof (add addSubst liftNext varNext leftZero)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFoldTargets (loopGraph scratchGraph)
open NumberedWindowInternalSparsePositiveFoldOpenChecks (exact_OpenFoldBase exact_OpenNilRetention)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof (moveFuel loopIntro)
open NumberedWindowInternalSparsePositiveIterationBindingProof (loopSubst scratchRename)
open NumberedWindowInternalSparsePositiveIterationTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Use the retained arithmetic Nat induction rule on extra fuel, at the
same original recursor. No standard evaluation equality is imported. -/
theorem extraResult (raw : Program 5) (p : Program 3)
    (out fuel extra c ty start cert current : OTerm α)
    (atFuel : Nonempty (Derivation body Γ (loopGraph raw p out fuel c ty start cert)))
    (done : Nonempty (Derivation body Γ (scratchGraph out z current))) :
    Nonempty (Derivation body Γ (loopGraph raw p out (add fuel extra) c ty start cert)) := by
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let j : α → α ⊕ Fin 1 := Sum.inl
  let theta := loopGraph raw p (out.relabel j) (add (fuel.relabel j) v)
    (c.relabel j) (ty.relabel j) (start.relabel j) (cert.relabel j)
  have atZero := moveFuel raw p out fuel (add fuel z) c ty start cert ⟨symm (addZero fuel)⟩ atFuel
  have base : Derivation body Γ (instantiate theta (emb z)) := by
    simp only [theta,instantiate,bindEmbedding,loopSubst,addSubst,j,liftBind,v,varBind]
    exact Classical.choice atZero
  let Δ := theta :: Γ.map weaken
  have ih : Nonempty (Derivation body Δ theta) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have moved := renameInto done j Δ (fun q h => List.mem_cons_of_mem _
    (List.mem_map.mpr ⟨q,h,rfl⟩))
  rw [scratchRename,zRelabel] at moved
  let n := add (fuel.relabel j) v
  let out' := out.relabel j
  let c' := c.relabel j
  let ty' := ty.relabel j
  let start' := start.relabel j
  let cert' := cert.relabel j
  have nilStep := closedApply
    (exact_OpenNilRetention body (raw) (p) (α ⊕ Fin 1) n out' c' ty' start' cert' (current.relabel j)) moved
  have after := loopIntro raw p out' out' n c' ty' start' cert' ih nilStep
  have next := moveFuel raw p out' (suc n) (add (fuel.relabel j) (suc v)) c' ty' start' cert'
    ⟨symm (addSucc (fuel.relabel j) v)⟩ after
  have step : Derivation body (theta :: Γ.map weaken) (successorInstance theta) := by
    simp only [theta,successorInstance,nextEmbedding,loopSubst,addSubst,j,liftNext,v,varNext]
    exact Classical.choice next
  have proved := Derivation.universalElimination (emb extra) (natInduction theta base step)
  simpa only [theta,instantiate,bindEmbedding,loopSubst,addSubst,j,liftBind,v,varBind]
    using (Nonempty.intro proved)

theorem extra : OpenTerminalExtraFuel := by
  intro body raw p α out fuel e c ty start cert cur
  let a := loopGraph raw p out fuel c ty start cert ⊓ scratchGraph out z cur
  have both : Derivation body [a] a := Derivation.hypothesis List.mem_cons_self
  obtain ⟨d⟩ := extraResult raw p out fuel e c ty start cert cur
    ⟨Derivation.conjunctionLeft both⟩ ⟨Derivation.conjunctionRight both⟩
  exact ⟨Derivation.implicationIntroduction d⟩

theorem zeroLoop : OpenTerminalNilLoop := by
  intro body raw p α out fuel c ty current
  let a := scratchGraph out z current
  have given : Nonempty (Derivation body [a] a) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have atZero := closedApply (exact_OpenFoldBase body raw p α out c ty current z) given
  have more := extraResult raw p out z fuel c ty current z current atZero given
  obtain ⟨d⟩ := moveFuel raw p out (add z fuel) fuel c ty current z ⟨leftZero fuel⟩ more
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationTerminalProof
