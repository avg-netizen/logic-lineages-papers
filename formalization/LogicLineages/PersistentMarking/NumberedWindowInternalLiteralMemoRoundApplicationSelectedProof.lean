module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoRoundApplicationInductionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnEdgeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoRoundApplicationSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoRoundApplicationSelectedProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (programRename compositionValue projectionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparsePackedLeast (poolAtSeed)
open NumberedWindowInternalSparseDirectedRounds (members membersTape poolLength)
open NumberedWindowInternalSparseOpenRoundsChecks (exact_OpenMembersAtLength)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalLiteralPackedLeastOnProof
open NumberedWindowInternalLiteralLeastOnAtPoolsProof (seedOn)
open NumberedWindowInternalLiteralLeastOnEdgeProof (exact_OpenLeastOnSeedReport)
open NumberedWindowInternalLiteralLeastOnMinimumProof (exact_OpenLeastOnSelected)
open NumberedWindowInternalLiteralMemoRoundApplicationMotiveProof
open NumberedWindowInternalLiteralMemoRoundApplicationSyntaxProof (motiveRename stepRename)
open NumberedWindowInternalLiteralMemoRoundApplicationInductionProof (exact_OpenMemoRoundApplicationLeastAt)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem poolArgs (Cf : Program 3) (sf : Settings) (xs : Fin 3 → OTerm α) (vertices : OTerm α)
    (v : Nonempty (Derivation body Γ (unary (scratchVertices Cf sf) vertices (xs 2)))) (k : Fin 4) :
    Nonempty (Derivation body Γ (programGraph
      ((![poolAtSeed Cf sf,.projection 0,.projection 1,.projection 2] : Fin 4 → Program 3) k)
      (membersTape vertices (xs 0) (xs 1) (xs 2) k) xs)) := by
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c => ?_) b) a) k
  · apply compositionValue (scratchVertices Cf sf) (fun _ : Fin 1 => .projection 2)
      vertices xs ![xs 2] v
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 2 xs
  · exact projectionValue 0 xs
  · exact projectionValue 1 xs
  · obtain rfl := Fin.eq_zero c
    exact projectionValue 2 xs

/-- The application motive transfers to the actual selected minimum of
either child's physical rounds. The parent and child use arbitrary
explicit edge checkers; they may be the same concrete memo program. -/
theorem exact_OpenMemoSelectedApplication
    (Cf : Program 3) (E : Program 4) (sf : Settings) (N : Program 1) (C : Program 3)
    (Q : Program 4) (varyArgument : Bool) (s : Settings)
    (fctx fty seed selected ctx ty dom cod fixed μ m : OTerm α)
    (step : ApplicationEdgeStepAt E N C Q varyArgument s body Γ fctx fty ctx ty dom cod fixed μ m)
    (held : Nonempty (Derivation body Γ (appMotive N C Q varyArgument s ctx ty dom cod fixed μ m seed)))
    (least : Nonempty (Derivation body Γ (leastOnGraph Cf E sf fctx fty seed selected))) :
    Nonempty (Derivation body Γ (appMotive N C Q varyArgument s ctx ty dom cod fixed μ m selected)) := by
  apply exact_OpenLeastOnSeedReport Cf E sf fctx fty seed selected _ least
  intro β j Δ verts pool keep report
  rw [motiveRename]
  obtain ⟨rep⟩ := report
  let c := fctx.relabel j
  let t := fty.relabel j
  let f := seed.relabel j
  let pick := selected.relabel j
  let xs : Fin 3 → OTerm β := ![c,t,f]
  have pooled : Nonempty (Derivation body Δ (programGraph (membersAtSeedOn Cf E sf) pool xs)) :=
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight rep)⟩
  have atV : Nonempty (Derivation body Δ (unary (scratchVertices Cf sf) verts (xs 2))) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight rep)⟩
  have hit := exact_OpenLeastOnSelected Cf E sf c t f pool pick
    ⟨Derivation.conjunctionLeft rep⟩ pooled
  have computed : Nonempty (Derivation body Δ (programGraph (members E) pool (membersTape verts c t f))) :=
    compositionRecover (members E) ![poolAtSeed Cf sf,.projection 0,.projection 1,.projection 2]
      pool xs (membersTape verts c t f) pooled (poolArgs Cf sf xs verts atV)
  have old := renameInto held j Δ keep
  rw [motiveRename] at old
  have step' := stepRename N C Q varyArgument s E fctx fty ctx ty dom cod fixed μ m step j Δ keep
  apply programCases poolLength ![verts] _
  intro γ n Θ fuel stay bound
  rw [motiveRename]
  rw [unaryInputsRename] at bound
  have rr := renameInto computed n Θ stay
  simp only [programRename,membersTape,quadInputsRename] at rr
  have h := renameInto hit n Θ stay
  rw [graphRename] at h
  have seed' := renameInto old n Θ stay
  rw [motiveRename] at seed'
  have st := stepRename N C Q varyArgument s E _ _ _ _ _ _ _ _ _ step' n Θ stay
  obtain ⟨len⟩ := exact_OpenMembersAtLength E body γ Θ (pool.relabel n) fuel
    (verts.relabel n) (c.relabel n) (t.relabel n) (f.relabel n)
  obtain ⟨l⟩ := bound
  obtain ⟨r⟩ := rr
  have line := Derivation.implicationElimination (Derivation.conjunctionLeft
    (Derivation.implicationElimination len l)) r
  exact exact_OpenMemoRoundApplicationLeastAt E N C Q varyArgument s body γ Θ fuel (verts.relabel n)
    (c.relabel n) (t.relabel n) (f.relabel n) (pool.relabel n) (pick.relabel n)
    ((ctx.relabel j).relabel n) ((ty.relabel j).relabel n) ((dom.relabel j).relabel n)
    ((cod.relabel j).relabel n) ((fixed.relabel j).relabel n) ((μ.relabel j).relabel n)
    ((m.relabel j).relabel n) st seed' ⟨line⟩ h

#print axioms exact_OpenMemoSelectedApplication
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoRoundApplicationSelectedProof
