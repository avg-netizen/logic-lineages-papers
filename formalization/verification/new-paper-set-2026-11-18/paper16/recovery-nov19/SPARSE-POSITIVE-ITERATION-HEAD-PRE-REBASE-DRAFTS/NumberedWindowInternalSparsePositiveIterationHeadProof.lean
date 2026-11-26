module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationHeadInductionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationHeadProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (outputTransport)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFold (iterateState)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph stepGraph)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof
open NumberedWindowInternalSparsePositiveIterationTargets
open NumberedWindowInternalSparsePositiveIterationHeadSyntaxProof
open NumberedWindowInternalSparsePositiveIterationHeadCompareProof (compareAt)
open NumberedWindowInternalSparsePositiveIterationHeadInductionProof (allFuel)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem toNewGraph (raw : Program 5) (least : Program 3) (p : Plan α)
    (fuel out : OTerm α)
    (checked : Nonempty (Derivation body Γ (sameAt raw least fuel p)))
    (prior : Nonempty (Derivation body Γ (oldLoop raw least p out (suc fuel)))) :
    Nonempty (Derivation body Γ (newLoop raw least p out fuel)) := by
  apply programCases (iterateState raw least) (loopArgs fuel p.context p.ty p.nextCurrent p.nextCertificate) _
  intro β j Δ v hJ actual
  change Nonempty (Derivation body Δ
    ((programGraph (iterateState raw least) out (loopArgs fuel p.context p.ty p.nextCurrent p.nextCertificate)).relabel j))
  rw [loopArgsRename] at actual
  rw [ID1Completion.InternalControlGraphSupportProof.programRename,loopArgsRename]
  have old := moveLoop j Δ hJ raw least out (suc fuel) p.context p.ty
    p.originalCurrent p.originalCertificate prior
  rw [sucRelabel] at old
  have same := renameInto checked j Δ hJ
  rw [sameAtRename] at same
  let p' := p.map (fun t => t.relabel j)
  obtain ⟨eq⟩ := compareAt raw least p' (fuel.relabel j) (out.relabel j) v same old actual
  exact (outputTransport (iterateState raw least) v (out.relabel j)
      (loopArgs (fuel.relabel j) p'.context p'.ty p'.nextCurrent p'.nextCertificate) ⟨symm eq⟩ actual)

private theorem toOldGraph (raw : Program 5) (least : Program 3) (p : Plan α)
    (fuel out : OTerm α)
    (checked : Nonempty (Derivation body Γ (sameAt raw least fuel p)))
    (prior : Nonempty (Derivation body Γ (newLoop raw least p out fuel))) :
    Nonempty (Derivation body Γ (oldLoop raw least p out (suc fuel))) := by
  apply programCases (iterateState raw least)
    (loopArgs (suc fuel) p.context p.ty p.originalCurrent p.originalCertificate) _
  intro β j Δ v hJ actual
  change Nonempty (Derivation body Δ
    ((programGraph (iterateState raw least) out
      (loopArgs (suc fuel) p.context p.ty p.originalCurrent p.originalCertificate)).relabel j))
  rw [loopArgsRename,sucRelabel] at actual
  rw [ID1Completion.InternalControlGraphSupportProof.programRename,loopArgsRename,sucRelabel]
  have new := moveLoop j Δ hJ raw least out fuel p.context p.ty p.nextCurrent p.nextCertificate prior
  have same := renameInto checked j Δ hJ
  rw [sameAtRename] at same
  let p' := p.map (fun t => t.relabel j)
  have eq := compareAt raw least p' (fuel.relabel j) v (out.relabel j) same actual new
  exact (outputTransport (iterateState raw least) v (out.relabel j)
      (loopArgs (suc (fuel.relabel j)) p'.context p'.ty p'.originalCurrent p'.originalCertificate) eq actual)

theorem shift : OpenHeadFirstShift := by
  intro body raw least α out fuel c ty oldCurrent oldCert nextCurrent nextCert old new
  let p : Plan α := ⟨c,ty,oldCurrent,oldCert,nextCurrent,nextCert⟩
  let linked := scratchGraph old oldCert oldCurrent ⊓ (scratchGraph new nextCert nextCurrent ⊓
    stepGraph raw least new z old c ty oldCurrent oldCert)
  let a := oldLoop raw least p out (suc fuel)
  let b := newLoop raw least p out fuel
  have link : Derivation body [linked] linked := Derivation.hypothesis List.mem_cons_self
  obtain ⟨total⟩ := allFuel raw least p fuel old new
    ⟨Derivation.conjunctionLeft link⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight link)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight link)⟩
  obtain ⟨forward⟩ := toNewGraph raw least p fuel out
    ⟨addHyp total a⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨backward⟩ := toOldGraph raw least p fuel out
    ⟨addHyp total b⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction backward))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationHeadProof
