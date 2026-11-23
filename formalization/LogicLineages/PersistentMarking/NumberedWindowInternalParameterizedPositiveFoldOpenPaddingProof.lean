module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationBindingProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenLoopProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenPaddingProof
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
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph)
open NumberedWindowInternalParameterizedPositiveFold
open NumberedWindowInternalParameterizedPositiveFoldOpenLoopProof
open NumberedWindowInternalSparsePositiveFold
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof (stateParts call6)
open NumberedWindowInternalSparseFieldCell (cellGood)
open ID1Completion.InternalAcceptance (branch)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro)
open ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalRecursionGraphSuccessorIntroductionProof (recursionSuccessorIntroduction)
open NumberedWindowInternalSparsePositiveIterationBindingProof (loopArgsSubst scratchRename)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof (loopArgs)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}


private theorem loopSubst {α β : Type} (A : Program 4)
    (out fuel c ty start cert : OTerm α) (ts : α → OTerm β) :
    (loopAt A out fuel c ty start cert).subst (fun a => emb (ts a)) =
      loopAt A (out.subst ts) (fuel.subst ts) (c.subst ts) (ty.subst ts)
        (start.subst ts) (cert.subst ts) := by
  change (programGraph (iterateAt A) out (loopArgs fuel c ty start cert)).subst
    (fun a => emb (ts a)) = _
  rw [programSubst,loopArgsSubst] <;> rfl

private theorem nilRetention (A : Program 4) (k prior c ty start cert cur : OTerm α)
    (done : Nonempty (Derivation body Γ (scratchGraph prior z cur))) :
    Nonempty (Derivation body Γ (programGraph (stepAt A) prior (call6 k prior c ty start cert))) := by
  let xs := call6 k prior c ty start cert
  have read := (stateParts z cur k prior c ty start cert done).1
  exact zeroBranchIntro scratchCursor (.projection 1)
    (branch (onCursor cellGood) dead (updateAt A)) prior xs read
    (projectionValue (1 : Fin 6) xs)

/-- Use the retained arithmetic Nat induction rule on extra fuel, at the
same original recursor. No standard evaluation equality is imported. -/
theorem exact_OpenParameterizedLoopPadding (A : Program 4)
    (out fuel extra c ty start cert current : OTerm α)
    (atFuel : Nonempty (Derivation body Γ (loopAt A out fuel c ty start cert)))
    (done : Nonempty (Derivation body Γ (scratchGraph out z current))) :
    Nonempty (Derivation body Γ (loopAt A out (add fuel extra) c ty start cert)) := by
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let j : α → α ⊕ Fin 1 := Sum.inl
  let theta := loopAt A (out.relabel j) (add (fuel.relabel j) v)
    (c.relabel j) (ty.relabel j) (start.relabel j) (cert.relabel j)
  have atZero := exact_OpenParameterizedLoopFuelTransport A out fuel (add fuel z) c ty start cert ⟨symm (addZero fuel)⟩ atFuel
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
  have nilStep := nilRetention A n out' c' ty' start' cert' (current.relabel j) moved
  have after : Nonempty (Derivation body Δ (loopAt A out' (suc n) c' ty' start' cert')) :=
    recursionSuccessorIntroduction Δ (OrdinaryArithmetic.graphFormula initial)
      (OrdinaryArithmetic.graphFormula (stepAt A)) out' n out' ![c',ty',start',cert'] ih nilStep
  have next := exact_OpenParameterizedLoopFuelTransport A out' (suc n) (add (fuel.relabel j) (suc v)) c' ty' start' cert'
    ⟨symm (addSucc (fuel.relabel j) v)⟩ after
  have step : Derivation body (theta :: Γ.map weaken) (successorInstance theta) := by
    simp only [theta,successorInstance,nextEmbedding,loopSubst,addSubst,j,liftNext,v,varNext]
    exact Classical.choice next
  have proved := Derivation.universalElimination (emb extra) (natInduction theta base step)
  simpa only [theta,instantiate,bindEmbedding,loopSubst,addSubst,j,liftBind,v,varBind]
    using (Nonempty.intro proved)


#print axioms exact_OpenParameterizedLoopPadding
end LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenPaddingProof
