module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundsInclusionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundsInclusionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename headTransport zeroSuccessorCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseDirectedFilter (cell)
open NumberedWindowInternalSparseDirectedRounds
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseOpenRoundsChecks
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename quadInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseRoundsInclusionTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem tapeRename {α β : Type} (n vertices ctx ty seed : OTerm α) (j : α → β) :
    (fun i => (roundsTape n vertices ctx ty seed i).relabel j) =
      roundsTape (n.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) := by
  funext i
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c =>
    Fin.cases ?_ (fun d => Fin.cases ?_ (fun e => Fin.elim0 e) d) c) b) a) i <;> rfl

private theorem roundRename {α β : Type} (E : Program 4)
    (out n vertices ctx ty seed : OTerm α) (j : α → β) :
    (roundGraph E out n vertices ctx ty seed).relabel j = roundGraph E (out.relabel j)
      (n.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) := by
  simp only [roundGraph,programRename,tapeRename]

private theorem atZero (E : Program 4) (subset : PassIncluded (constantZero 4))
    (out vertices ctx ty seed k : OTerm α)
    (round : Nonempty (Derivation body Γ (roundGraph E out z vertices ctx ty seed)))
    (member : Nonempty (Derivation body Γ (memberGraph out k))) :
    Nonempty (Derivation body Γ (memberGraph vertices k)) := by
  apply programCases consCode ![seed,z] _
  intro β j Δ singleton keep hs
  rw [graphRename]
  rw [binaryInputsRename,zRelabel] at hs
  have hr := renameInto round j Δ keep
  rw [roundRename,zRelabel] at hr
  have hm := renameInto member j Δ keep
  rw [graphRename] at hm
  obtain ⟨step⟩ := exact_OpenRoundZero E body β Δ (out.relabel j) (vertices.relabel j)
    (ctx.relabel j) (ty.relabel j) (seed.relabel j) singleton
  obtain ⟨inc⟩ := subset body β Δ (out.relabel j) (vertices.relabel j) singleton
    (ctx.relabel j) (ty.relabel j) (k.relabel j)
  obtain ⟨h⟩ := hs
  obtain ⟨r⟩ := hr
  obtain ⟨m⟩ := hm
  have pass := Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination step h)) r
  exact ⟨Derivation.implicationElimination inc (Derivation.conjunctionIntroduction pass m)⟩

private theorem atSucc (E : Program 4) (subset : PassIncluded E)
    (out fuel vertices ctx ty seed k : OTerm α)
    (round : Nonempty (Derivation body Γ (roundGraph E out (suc fuel) vertices ctx ty seed)))
    (member : Nonempty (Derivation body Γ (memberGraph out k))) :
    Nonempty (Derivation body Γ (memberGraph vertices k)) := by
  apply programCases (rounds E) (roundsTape fuel vertices ctx ty seed) _
  intro β j Δ previous keep hp
  rw [graphRename]
  rw [tapeRename] at hp
  have hr := renameInto round j Δ keep
  rw [roundRename,sucRelabel] at hr
  have hm := renameInto member j Δ keep
  rw [graphRename] at hm
  obtain ⟨step⟩ := exact_OpenRoundSuccessor E body β Δ (out.relabel j) (fuel.relabel j)
    (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) previous
  obtain ⟨inc⟩ := subset body β Δ (out.relabel j) (vertices.relabel j) previous
    (ctx.relabel j) (ty.relabel j) (k.relabel j)
  obtain ⟨h⟩ := hp
  obtain ⟨r⟩ := hr
  obtain ⟨m⟩ := hm
  have pass := Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination step h)) r
  exact ⟨Derivation.implicationElimination inc (Derivation.conjunctionIntroduction pass m)⟩

private theorem allFuels (E : Program 4) (base : PassIncluded (constantZero 4))
    (step : PassIncluded E) (out fuel vertices ctx ty seed k : OTerm α)
    (round : Nonempty (Derivation body Γ (roundGraph E out fuel vertices ctx ty seed)))
    (member : Nonempty (Derivation body Γ (memberGraph out k))) :
    Nonempty (Derivation body Γ (memberGraph vertices k)) := by
  apply zeroSuccessorCases Γ fuel _
  · obtain ⟨r⟩ := round
    obtain ⟨m⟩ := member
    let Δ := eqn fuel z :: Γ
    have moved : Nonempty (Derivation body Δ (roundGraph E out z vertices ctx ty seed)) :=
      headTransport (rounds E) out fuel z (membersTape vertices ctx ty seed)
        ⟨Derivation.hypothesis List.mem_cons_self⟩
        ⟨ID1Completion.InternalBetaTotalityProof.addHyp r _⟩
    exact atZero E base out vertices ctx ty seed k moved
      ⟨ID1Completion.InternalBetaTotalityProof.addHyp m _⟩
  · intro β j Δ previous keep eq
    rw [graphRename]
    have rr := renameInto round j Δ keep
    rw [roundRename] at rr
    have mm := renameInto member j Δ keep
    rw [graphRename] at mm
    have moved := headTransport (rounds E) (out.relabel j) (fuel.relabel j) (suc previous)
      (membersTape (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)) eq rr
    exact atSucc E step (out.relabel j) previous (vertices.relabel j) (ctx.relabel j)
      (ty.relabel j) (seed.relabel j) (k.relabel j) moved mm

private theorem atMembers (E : Program 4) (inc : RoundsIncluded E)
    (out vertices ctx ty seed k : OTerm α)
    (selected : Nonempty (Derivation body Γ
      (programGraph (members E) out (membersTape vertices ctx ty seed))))
    (member : Nonempty (Derivation body Γ (memberGraph out k))) :
    Nonempty (Derivation body Γ (memberGraph vertices k)) := by
  apply programCases poolLength ![vertices] _
  intro β j Δ fuel keep len
  rw [graphRename]
  rw [unaryInputsRename] at len
  have mm := renameInto member j Δ keep
  rw [graphRename] at mm
  have ss := renameInto selected j Δ keep
  simp only [programRename,membersTape,quadInputsRename] at ss
  obtain ⟨atLength⟩ := exact_OpenMembersAtLength E body β Δ (out.relabel j) fuel
    (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  obtain ⟨rule⟩ := inc body β Δ (out.relabel j) fuel (vertices.relabel j) (ctx.relabel j)
    (ty.relabel j) (seed.relabel j) (k.relabel j)
  obtain ⟨l⟩ := len
  obtain ⟨s⟩ := ss
  obtain ⟨m⟩ := mm
  have rr := Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination atLength l)) s
  exact ⟨Derivation.implicationElimination rule (Derivation.conjunctionIntroduction rr m)⟩

theorem transport : ExactRoundsInclusionFromPass := by
  intro E base step
  have roundsRule : RoundsIncluded E := by
    intro body α Γ out fuel vertices ctx ty seed k
    let P := roundGraph E out fuel vertices ctx ty seed ⊓ memberGraph out k
    have h : Derivation body (P :: Γ) P := Derivation.hypothesis List.mem_cons_self
    obtain ⟨proof⟩ := allFuels E base step out fuel vertices ctx ty seed k
      ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionRight h⟩
    exact ⟨Derivation.implicationIntroduction proof⟩
  refine ⟨roundsRule,?_⟩
  intro body α Γ out vertices ctx ty seed k
  let P := programGraph (members E) out (membersTape vertices ctx ty seed) ⊓ memberGraph out k
  have h : Derivation body (P :: Γ) P := Derivation.hypothesis List.mem_cons_self
  obtain ⟨proof⟩ := atMembers E roundsRule out vertices ctx ty seed k
    ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionRight h⟩
  exact ⟨Derivation.implicationIntroduction proof⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundsInclusionProof
