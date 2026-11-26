module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoRoundApplicationMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoRoundApplicationSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundOriginChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoRoundApplicationInductionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalClosedProgramsBindingProof (introduction)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb eqn z suc sucRelabel zRelabel bindEmbedding nextEmbedding nextTerm nextLift liftBind varBind)
open ID1Completion.InternalTagArithmeticSupportProof (natInduction)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseRoundWindowMotiveProof (roundRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseRoundOriginChecks (exact_ZeroRoundOrigin exact_SuccessorRoundOrigin)
open NumberedWindowInternalSparseRetainedScanChecks (exact_RetainedPredecessor)
open NumberedWindowInternalSparseDirectedSeen (seenWitness witnessRow acceptEdge)
open NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof (witnessBinder witnessUnfold)
open NumberedWindowInternalSparseDirectedRounds (rounds roundsTape)
open NumberedWindowInternalLiteralMemoRoundApplicationSyntaxProof
  (matrix AtCount atCountSubst atCountRename applyAt moveMotive motiveRename stepRename)
open NumberedWindowInternalLiteralMemoRoundApplicationMotiveProof

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)}
variable (N : Program 1) (C : Program 3) (Q : Program 4) (varyArgument : Bool) (s : Settings) (E : Program 4)

private theorem baseCore {α : Type} {Γ : List (Formula α)}
    (vertices fctx fty seed ctx ty dom cod arg μ m out k : OTerm α)
    (seedM : Nonempty (Derivation body Γ (appMotive N C Q varyArgument s ctx ty dom cod arg μ m seed)))
    (round : Derivation body Γ (roundGraph E out z vertices fctx fty seed))
    (member : Derivation body Γ (memberGraph out k)) :
    Nonempty (Derivation body Γ (appMotive N C Q varyArgument s ctx ty dom cod arg μ m k)) := by
  obtain ⟨origin⟩ := exact_ZeroRoundOrigin exact_RetainedPredecessor E body α Γ out vertices fctx fty seed k
  have given := Derivation.implicationElimination (Derivation.conjunctionLeft
    (Derivation.implicationElimination origin round)) member
  obtain ⟨sm⟩ := seedM
  exact moveMotive N C Q varyArgument s ctx ty dom cod arg μ m seed k (Derivation.conjunctionRight given) sm

private theorem fromWitness {α : Type} {Γ : List (Formula α)}
    (vertices fctx fty seed ctx ty dom cod arg μ m i before k : OTerm α)
    (step : ApplicationEdgeStepAt E N C Q varyArgument s body Γ fctx fty ctx ty dom cod arg μ m)
    (old : Nonempty (Derivation body Γ
      (AtCount N C Q varyArgument s E vertices fctx fty seed ctx ty dom cod arg μ m i)))
    (prior : Nonempty (Derivation body Γ (roundGraph E before i vertices fctx fty seed)))
    (witness : Derivation body Γ (seenWitness E before fctx fty k)) :
    Nonempty (Derivation body Γ (appMotive N C Q varyArgument s ctx ty dom cod arg μ m k)) := by
  rw [witnessUnfold] at witness
  let j : α → α ⊕ Fin 1 := Sum.inl
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let Δ := witnessBinder E before fctx fty k :: Γ.map weaken
  have keep (p : Formula α) (hp : p ∈ Γ) : p.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have old' := renameInto old j Δ keep
  have prior' := renameInto prior j Δ keep
  rw [atCountRename] at old'
  rw [roundRename] at prior'
  have row : Derivation body Δ
      (witnessRow E (before.relabel j) (fctx.relabel j) (fty.relabel j) w (k.relabel j)) :=
    Derivation.hypothesis List.mem_cons_self
  obtain ⟨atW⟩ := applyAt N C Q varyArgument s E (vertices.relabel j) (fctx.relabel j) (fty.relabel j)
    (seed.relabel j) (ctx.relabel j) (ty.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j)
    (μ.relabel j) (m.relabel j) (i.relabel j) (before.relabel j) w old' prior'
    ⟨Derivation.conjunctionLeft row⟩
  let eq := eqn w (k.relabel j)
  let edge := acceptEdge E (fctx.relabel j) (fty.relabel j) w (k.relabel j)
  obtain ⟨a⟩ := moveMotive (Γ := eq :: Δ) N C Q varyArgument s (ctx.relabel j) (ty.relabel j) (dom.relabel j)
    (cod.relabel j) (arg.relabel j) (μ.relabel j) (m.relabel j) w (k.relabel j)
    (Derivation.hypothesis List.mem_cons_self) (addHyp atW eq)
  obtain ⟨b⟩ := step (α ⊕ Fin 1) j (edge :: Δ) w (k.relabel j)
    (fun p hp => List.mem_cons_of_mem _ (keep p hp)) ⟨Derivation.hypothesis List.mem_cons_self⟩
    ⟨addHyp atW edge⟩
  have result := disjunctionElimination (Derivation.conjunctionRight row)
    (Derivation.implicationIntroduction a) (Derivation.implicationIntroduction b)
  have final : Derivation body Δ (weaken (appMotive N C Q varyArgument s ctx ty dom cod arg μ m k)) := by
    change Derivation body Δ ((appMotive N C Q varyArgument s ctx ty dom cod arg μ m k).relabel j)
    rwa [motiveRename]
  exact ⟨Derivation.existentialElimination witness final⟩

private theorem stepCore {α : Type} {Γ : List (Formula α)}
    (vertices fctx fty seed ctx ty dom cod arg μ m i out k : OTerm α)
    (step : ApplicationEdgeStepAt E N C Q varyArgument s body Γ fctx fty ctx ty dom cod arg μ m)
    (old : Nonempty (Derivation body Γ
      (AtCount N C Q varyArgument s E vertices fctx fty seed ctx ty dom cod arg μ m i)))
    (round : Nonempty (Derivation body Γ (roundGraph E out (suc i) vertices fctx fty seed)))
    (member : Nonempty (Derivation body Γ (memberGraph out k))) :
    Nonempty (Derivation body Γ (appMotive N C Q varyArgument s ctx ty dom cod arg μ m k)) := by
  apply programCases (rounds E) (roundsTape i vertices fctx fty seed) _
  intro β j Δ before keep prior
  rw [motiveRename]
  have ih := renameInto old j Δ keep
  rw [atCountRename] at ih
  have r := renameInto round j Δ keep
  have mem := renameInto member j Δ keep
  simp only [roundRename,sucRelabel] at r
  rw [graphRename] at mem
  have tape : (fun k => (roundsTape i vertices fctx fty seed k).relabel j) =
      roundsTape (i.relabel j) (vertices.relabel j) (fctx.relabel j) (fty.relabel j) (seed.relabel j) := by
    funext k
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c =>
      Fin.cases ?_ (fun d => Fin.cases ?_ (fun e => Fin.elim0 e) d) c) b) a) k <;> rfl
  rw [tape] at prior
  obtain ⟨p⟩ := prior
  obtain ⟨r⟩ := r
  obtain ⟨mem⟩ := mem
  obtain ⟨law⟩ := exact_SuccessorRoundOrigin exact_RetainedPredecessor E body β Δ before
    (out.relabel j) (i.relabel j) (vertices.relabel j) (fctx.relabel j) (fty.relabel j) (seed.relabel j) (k.relabel j)
  have found := Derivation.implicationElimination (Derivation.conjunctionLeft
    (Derivation.implicationElimination law (Derivation.conjunctionIntroduction p r))) mem
  exact fromWitness N C Q varyArgument s E _ _ _ _ _ _ _ _ _ _ _ _ before _
    (stepRename N C Q varyArgument s E fctx fty ctx ty dom cod arg μ m step j Δ keep) ih ⟨p⟩
    (Derivation.conjunctionRight found)

private theorem zeroRow {α : Type} {Δ : List (Formula α)}
    (vertices fctx fty seed ctx ty dom cod arg μ m : OTerm α)
    (seedM : Nonempty (Derivation body Δ (appMotive N C Q varyArgument s ctx ty dom cod arg μ m seed))) :
    Nonempty (Derivation body Δ (AtCount N C Q varyArgument s E vertices fctx fty seed ctx ty dom cod arg μ m z)) := by
  apply introduction body α 2 Δ (matrix N C Q varyArgument s E vertices fctx fty seed ctx ty dom cod arg μ m z)
  let out : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let k : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  let A := roundGraph E out z (vertices.relabel Sum.inl) (fctx.relabel Sum.inl) (fty.relabel Sum.inl)
    (seed.relabel Sum.inl) ⊓ memberGraph out k
  let Γ := A :: Δ.map (fun p => p.relabel Sum.inl)
  have h : Derivation body Γ A := Derivation.hypothesis List.mem_cons_self
  have sm := renameInto seedM (Sum.inl : α → α ⊕ Fin 2) Γ
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [motiveRename] at sm
  obtain ⟨d⟩ := baseCore N C Q varyArgument s E _ _ _ _ _ _ _ _ _ _ _ out k sm
    (Derivation.conjunctionLeft h) (Derivation.conjunctionRight h)
  simpa only [matrix,zRelabel] using Nonempty.intro (Derivation.implicationIntroduction d)

private theorem succRow {α : Type} {Δ : List (Formula α)}
    (vertices fctx fty seed ctx ty dom cod arg μ m : OTerm α)
    (step : ApplicationEdgeStepAt E N C Q varyArgument s body Δ fctx fty ctx ty dom cod arg μ m)
    (elapsed : OTerm α)
    (row : Nonempty (Derivation body Δ
      (AtCount N C Q varyArgument s E vertices fctx fty seed ctx ty dom cod arg μ m elapsed))) :
    Nonempty (Derivation body Δ
      (AtCount N C Q varyArgument s E vertices fctx fty seed ctx ty dom cod arg μ m (suc elapsed))) := by
  apply introduction body α 2 Δ (matrix N C Q varyArgument s E vertices fctx fty seed ctx ty dom cod arg μ m (suc elapsed))
  let out : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let k : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  let A := roundGraph E out (suc (elapsed.relabel Sum.inl)) (vertices.relabel Sum.inl)
    (fctx.relabel Sum.inl) (fty.relabel Sum.inl) (seed.relabel Sum.inl) ⊓ memberGraph out k
  let Γ := A :: Δ.map (fun p => p.relabel Sum.inl)
  have keep (p : Formula α) (hp : p ∈ Δ) : p.relabel (Sum.inl : α → α ⊕ Fin 2) ∈ Γ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have h : Derivation body Γ A := Derivation.hypothesis List.mem_cons_self
  have rr := renameInto row (Sum.inl : α → α ⊕ Fin 2) Γ keep
  rw [atCountRename] at rr
  have st := stepRename N C Q varyArgument s E fctx fty ctx ty dom cod arg μ m step (Sum.inl : α → α ⊕ Fin 2) Γ keep
  obtain ⟨d⟩ := stepCore N C Q varyArgument s E _ _ _ _ _ _ _ _ _ _ _ (elapsed.relabel Sum.inl) out k st rr
    ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionRight h⟩
  simpa only [matrix,sucRelabel] using Nonempty.intro (Derivation.implicationIntroduction d)

private theorem allCounts {α : Type} {Δ : List (Formula α)}
    (vertices fctx fty seed ctx ty dom cod arg μ m : OTerm α)
    (step : ApplicationEdgeStepAt E N C Q varyArgument s body Δ fctx fty ctx ty dom cod arg μ m)
    (seedM : Nonempty (Derivation body Δ (appMotive N C Q varyArgument s ctx ty dom cod arg μ m seed)))
    (count : OTerm α) :
    Nonempty (Derivation body Δ
      (AtCount N C Q varyArgument s E vertices fctx fty seed ctx ty dom cod arg μ m count)) := by
  let kk : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let l : OTerm α → OTerm (α ⊕ Fin 1) := fun t => t.relabel Sum.inl
  let theta : Formula (α ⊕ Fin 1) := AtCount N C Q varyArgument s E (l vertices) (l fctx) (l fty) (l seed)
    (l ctx) (l ty) (l dom) (l cod) (l arg) (l μ) (l m) kk
  have hz : Nonempty (Derivation body Δ (instantiate theta (emb z))) := by
    simpa only [theta,kk,l,instantiate,bindEmbedding,atCountSubst,liftBind,varBind] using
      (zeroRow (body := body) (Δ := Δ) N C Q varyArgument s E vertices fctx fty seed ctx ty dom cod arg μ m seedM)
  have hs : Nonempty (Derivation body (theta :: Δ.map weaken) (successorInstance theta)) := by
    have st := stepRename N C Q varyArgument s E fctx fty ctx ty dom cod arg μ m step (Sum.inl : α → α ⊕ Fin 1)
      (theta :: Δ.map weaken) (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    have h := succRow (body := body) (Δ := theta :: Δ.map weaken) N C Q varyArgument s E (l vertices) (l fctx)
      (l fty) (l seed) (l ctx) (l ty) (l dom) (l cod) (l arg) (l μ) (l m) st kk
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,kk,l,successorInstance,nextEmbedding,atCountSubst,nextTerm,nextLift,Term.subst,
      Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,kk,l,instantiate,bindEmbedding,atCountSubst,liftBind,varBind] using Nonempty.intro h

theorem exact_OpenMemoRoundApplicationLeastAt : ExactRoundApplicationLeastAt := by
  intro E N C Q varyArgument s body α Γ i vertices fctx fty seed out k ctx ty dom cod arg μ m step seedM round member
  exact applyAt N C Q varyArgument s E vertices fctx fty seed ctx ty dom cod arg μ m i out k
    (allCounts N C Q varyArgument s E vertices fctx fty seed ctx ty dom cod arg μ m step seedM i) round member

theorem exact_OpenMemoRoundApplicationLeast : ExactRoundApplicationLeast := by
  intro E N C Q varyArgument s paid body α Γ i vertices fctx fty seed out k ctx ty dom cod arg μ m
  let A := appMotive N C Q varyArgument s ctx ty dom cod arg μ m seed ⊓
    (roundGraph E out i vertices fctx fty seed ⊓ memberGraph out k)
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have step : ApplicationEdgeStepAt E N C Q varyArgument s body Δ fctx fty ctx ty dom cod arg μ m := by
    intro β j Θ w k' _ e mw
    obtain ⟨law⟩ := paid body β Θ (fctx.relabel j) (fty.relabel j) (ctx.relabel j) (ty.relabel j)
      (dom.relabel j) (cod.relabel j) (arg.relabel j) (μ.relabel j) (m.relabel j) w k'
    obtain ⟨e⟩ := e
    obtain ⟨mw⟩ := mw
    exact ⟨Derivation.implicationElimination law (Derivation.conjunctionIntroduction e mw)⟩
  obtain ⟨d⟩ := exact_OpenMemoRoundApplicationLeastAt E N C Q varyArgument s body α Δ i vertices fctx fty seed out k
    ctx ty dom cod arg μ m step ⟨Derivation.conjunctionLeft h⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight h)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight h)⟩
  exact ⟨Derivation.implicationIntroduction d⟩

#print axioms exact_OpenMemoRoundApplicationLeastAt
#print axioms exact_OpenMemoRoundApplicationLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoRoundApplicationInductionProof
