module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPackedLeastOnProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedBoundChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof


import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnMembersProof

open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalControlGraphSupportProof (compositionValue programRename projectionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalLiteralPackedLeastOnProof
open NumberedWindowInternalSparsePackedLeast (poolAtSeed contextOption)
open NumberedWindowInternalSparseOrderedMinimum (scratchMinimum)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open NumberedWindowInternalSparseMinimumBoundChecks (exact_OpenMemberHasBoundedMinimum)
open NumberedWindowInternalSparseMinimumBoundWitnessProof (casesValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (existsEmbeddedSubst liftTermSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding bindTerm liftBind varBind sucSubst)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseDirectedRounds (members membersTape poolLength)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalSparseOpenRoundsChecks (exact_OpenMembersAtLength)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseSeedBoundChecks (exact_SeedEveryRound)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}


theorem exact_OpenLeastOnSeedRetained (E : Program 4) (vertices ctx ty seed pool : OTerm α)
    (present : Nonempty (Derivation body Γ (memberGraph vertices seed)))
    (computed : Nonempty (Derivation body Γ (programGraph (members E) pool
      (membersTape vertices ctx ty seed)))) :
    Nonempty (Derivation body Γ (memberGraph pool seed)) := by
  apply programCases poolLength ![vertices] _
  intro β j Δ fuel keep length
  rw [graphRename]
  rw [unaryInputsRename] at length
  have hit := renameInto present j Δ keep
  rw [graphRename] at hit
  have selected := renameInto computed j Δ keep
  simp only [programRename,membersTape,quadInputsRename] at selected
  obtain ⟨length⟩ := length
  obtain ⟨hit⟩ := hit
  obtain ⟨selected⟩ := selected
  obtain ⟨atLength⟩ := exact_OpenMembersAtLength E body β Δ (pool.relabel j) fuel
    (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  have round := Derivation.implicationElimination (Derivation.conjunctionLeft
    (Derivation.implicationElimination atLength length)) selected
  obtain ⟨keepSeed⟩ := exact_SeedEveryRound E body β Δ (pool.relabel j) fuel
    (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  exact ⟨Derivation.implicationElimination keepSeed (Derivation.conjunctionIntroduction round hit)⟩

theorem exact_OpenLeastOnActualMembers (C : Program 3) (E : Program 4) (s : Settings)
    (ctx ty seed vertices pool : OTerm α)
    (cover : Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices seed)))
    (packed : Nonempty (Derivation body Γ (programGraph (membersAtSeedOn C E s) pool ![ctx,ty,seed]))) :
    Nonempty (Derivation body Γ (programGraph (members E) pool
      (membersTape vertices ctx ty seed))) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,seed]
  apply compositionRecover (members E)
    ![poolAtSeed C s,.projection 0,.projection 1,.projection 2]
    pool xs (membersTape vertices ctx ty seed) packed
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => ?_) k) j) i
  · apply compositionValue (scratchVertices C s) (fun _ : Fin 1 => .projection 2)
      vertices xs ![seed] cover
    intro k
    obtain rfl := Fin.eq_zero k
    exact projectionValue 2 xs
  · exact projectionValue 0 xs
  · exact projectionValue 1 xs
  · obtain rfl := Fin.eq_zero l
    exact projectionValue 2 xs

/-- The actual context-option and scratch minimum reassemble the same
literal packed program on any selected edge. -/
theorem exact_OpenLeastOnFromMinimum (C : Program 3) (E : Program 4) (s : Settings)
    (ctx ty seed payload pool out : OTerm α)
    (parsed : Nonempty (Derivation body Γ (programGraph contextOption (suc payload) ![ctx,ty,seed])))
    (computed : Nonempty (Derivation body Γ (programGraph (membersAtSeedOn C E s) pool ![ctx,ty,seed])))
    (minimum : Nonempty (Derivation body Γ (unary scratchMinimum out pool))) :
    Nonempty (Derivation body Γ (programGraph (packedLeastOn C E s) out ![ctx,ty,seed])) := by
  apply successorBranchIntro contextOption (constantZero 3) (minimumAtMembersOn C E s)
    out payload ![ctx,ty,seed] parsed
  apply compositionValue scratchMinimum (fun _ : Fin 1 => membersAtSeedOn C E s)
    out ![ctx,ty,seed] ![pool] minimum
  intro i
  obtain rfl := Fin.eq_zero i
  exact computed

/-- The open domain is represented by an actual successor report, not
a metalevel claim of evaluator totality. -/
def hasLeastOn {α : Type} (C : Program 3) (E : Program 4) (s : Settings)
    (ctx ty seed : OTerm α) : Formula α :=
  existsOne (leastOnGraph C E s (ctx.relabel Sum.inl) (ty.relabel Sum.inl)
    (seed.relabel Sum.inl) (.var (.inr 0)))

private theorem tripleSubst {α β : Type} (a b c : OTerm α) (ts : α → OTerm β) :
    (fun i => ((![a,b,c] : Fin 3 → OTerm α) i).subst ts) =
      ![a.subst ts,b.subst ts,c.subst ts] := by
  funext i
  refine Fin.cases ?_ (fun x => Fin.cases ?_ (fun y =>
    Fin.cases ?_ (fun noIndex => Fin.elim0 noIndex) y) x) i <;> rfl

theorem leastOnRename {α β : Type} (C : Program 3) (E : Program 4) (s : Settings)
    (ctx ty seed out : OTerm α) (j : α → β) :
    (leastOnGraph C E s ctx ty seed out).relabel j =
      leastOnGraph C E s (ctx.relabel j) (ty.relabel j) (seed.relabel j) (out.relabel j) := by
  simp only [leastOnGraph,programRename,tripleInputsRename,sucRelabel]

theorem hasOnRename {α β : Type} (C : Program 3) (E : Program 4) (s : Settings)
    (ctx ty seed : OTerm α) (j : α → β) :
    (hasLeastOn C E s ctx ty seed).relabel j =
      hasLeastOn C E s (ctx.relabel j) (ty.relabel j) (seed.relabel j) := by
  simp only [hasLeastOn,existsRename,leastOnRename,Term.relabel_relabel]
  rfl

theorem enterLeastOn (C : Program 3) (E : Program 4) (s : Settings) (ctx ty seed out : OTerm α)
    (d : Nonempty (Derivation body Γ (leastOnGraph C E s ctx ty seed out))) :
    Nonempty (Derivation body Γ (hasLeastOn C E s ctx ty seed)) := by
  let f := leastOnGraph C E s (ctx.relabel (Sum.inl : α → α ⊕ Fin 1))
    (ty.relabel Sum.inl) (seed.relabel Sum.inl) (.var (.inr 0))
  have h : instantiate f (emb out) = leastOnGraph C E s ctx ty seed out := by
    simp only [f,leastOnGraph,instantiate,bindEmbedding,programSubst,tripleSubst,sucSubst,liftBind,varBind]
  obtain ⟨d⟩ := d
  change Nonempty (Derivation body Γ (existsOne f))
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb out)
  rwa [h]

/-- Original context parse, real scratch cover, and seed membership
suffice for a selected least even for the enriched edge. -/
theorem exact_OpenLeastOnFromSeed (C : Program 3) (E : Program 4) (s : Settings)
    (ctx ty seed payload vertices : OTerm α)
    (parsed : Nonempty (Derivation body Γ (programGraph contextOption (suc payload) ![ctx,ty,seed])))
    (cover : Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices seed)))
    (hit : Nonempty (Derivation body Γ (memberGraph vertices seed))) :
    Nonempty (Derivation body Γ (hasLeastOn C E s ctx ty seed)) := by
  apply programCases (membersAtSeedOn C E s) ![ctx,ty,seed] _
  intro β j Δ pool keep computed
  rw [hasOnRename]
  rw [tripleInputsRename] at computed
  have cv := renameInto cover j Δ keep
  rw [unaryRename] at cv
  have ini := renameInto hit j Δ keep
  rw [graphRename] at ini
  have parser := renameInto parsed j Δ keep
  simp only [programRename,sucRelabel,tripleInputsRename] at parser
  have physical := exact_OpenLeastOnActualMembers C E s (ctx.relabel j) (ty.relabel j)
    (seed.relabel j) (vertices.relabel j) pool cv computed
  obtain ⟨present⟩ := exact_OpenLeastOnSeedRetained E (vertices.relabel j) (ctx.relabel j)
    (ty.relabel j) (seed.relabel j) pool ini physical
  obtain ⟨bound⟩ := exact_OpenMemberHasBoundedMinimum body β Δ pool (seed.relabel j)
  apply casesValue pool (seed.relabel j) _ ⟨Derivation.implicationElimination bound present⟩
  intro γ k Θ m keep' row
  rw [hasOnRename]
  have cp := renameInto computed k Θ keep'
  simp only [programRename,tripleInputsRename] at cp
  have pc := renameInto parser k Θ keep'
  simp only [programRename,sucRelabel,tripleInputsRename] at pc
  obtain ⟨d⟩ := row
  apply enterLeastOn C E s _ _ _ m
  exact exact_OpenLeastOnFromMinimum C E s _ _ _ ((payload.relabel j).relabel k) (pool.relabel k)
    (suc m) pc cp ⟨Derivation.conjunctionLeft d⟩

#print axioms exact_OpenLeastOnSeedRetained
#print axioms exact_OpenLeastOnActualMembers
#print axioms exact_OpenLeastOnFromMinimum
#print axioms hasOnRename
#print axioms enterLeastOn
#print axioms exact_OpenLeastOnFromSeed
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnMembersProof
