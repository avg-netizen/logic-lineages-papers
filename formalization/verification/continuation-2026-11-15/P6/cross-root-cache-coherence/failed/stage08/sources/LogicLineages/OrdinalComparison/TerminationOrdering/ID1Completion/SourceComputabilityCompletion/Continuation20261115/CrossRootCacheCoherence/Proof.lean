module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb sucRelabel zRelabel eqnRelabel)
open InternalRecursionGraphStepSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open InternalOriginalOrderSyntaxProof (ltF)
open InternalSquareRootArithmeticSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open SideProof PresenceProof InputProof InductionDefinitions

theorem rawStep (raw : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (AtRaw raw)) := by
  apply BindingProof.atRawIntro raw
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let r : OTerm (alpha ⊕ Fin 12) := raw.relabel Sum.inl
  let param : OTerm (alpha ⊕ Fin 12) := .var (.inr 0)
  let index1 : OTerm (alpha ⊕ Fin 12) := .var (.inr 1)
  let seed1 : OTerm (alpha ⊕ Fin 12) := .var (.inr 2)
  let depth1 : OTerm (alpha ⊕ Fin 12) := .var (.inr 3)
  let frontier1 : OTerm (alpha ⊕ Fin 12) := .var (.inr 4)
  let table1 : OTerm (alpha ⊕ Fin 12) := .var (.inr 5)
  let index2 : OTerm (alpha ⊕ Fin 12) := .var (.inr 6)
  let seed2 : OTerm (alpha ⊕ Fin 12) := .var (.inr 7)
  let depth2 : OTerm (alpha ⊕ Fin 12) := .var (.inr 8)
  let frontier2 : OTerm (alpha ⊕ Fin 12) := .var (.inr 9)
  let table2 : OTerm (alpha ⊕ Fin 12) := .var (.inr 10)
  let found : OTerm (alpha ⊕ Fin 12) := .var (.inr 11)
  let Theta := fields r param index1 seed1 depth1 frontier1 table1 index2 seed2 depth2 frontier2 table2 found :: Delta.map (fun q => q.relabel Sum.inl)
  change Derivation body Theta (result r param index1 seed1 depth1 frontier1 table1 index2 seed2 depth2 frontier2 table2 found)
  have hf : Nonempty (Derivation body Theta (fields r param index1 seed1 depth1 frontier1 table1 index2 seed2 depth2 frontier2 table2 found)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h0 := andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (hf))))))))))
  have h1 := andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (hf))))))))))
  have h2 := andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (hf)))))))))
  have h3 := andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (hf))))))))
  have h4 := andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (hf)))))))
  have h5 := andRight (andLeft (andLeft (andLeft (andLeft (andLeft (hf))))))
  have h6 := andRight (andLeft (andLeft (andLeft (andLeft (hf)))))
  have h7 := andRight (andLeft (andLeft (andLeft (hf))))
  have h8 := andRight (andLeft (andLeft (hf)))
  have h9 := andRight (andLeft (hf))
  have h10 := andRight (hf)
  have hij := InternalGraphCompositionFunctionalityProof.renameInto hi (Sum.inl : alpha → alpha ⊕ Fin 12) Theta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  simp only [InductionSyntaxProof.belowRawRename] at hij
  let s1 : Side body Theta r param := {
    index := index1, seed := seed1, depth := depth1, frontier := frontier1, table := table1,
    bounded := h0, subtraction := h1, front := h2, member := h3, tableGraph := h4 }
  let s2 : Side body Theta r param := {
    index := index2, seed := seed2, depth := depth2, frontier := frontier2, table := table2,
    bounded := h5, subtraction := h6, front := h7, member := h8, tableGraph := h9 }
  exact Classical.choice (CoreProof.close {
    s1 := s1, s2 := s2, found := found, below := hij, lookup := h10 })

theorem allRaw (raw : OTerm alpha) : Nonempty (Derivation body Delta (AtRaw raw)) :=
  BindingProof.rawInduction raw (fun _ _ r hi => rawStep r hi)

theorem cacheTransport : Targets.InternalCacheTransport := by
  intro body alpha Delta raw param index1 seed1 depth1 frontier1 table1 index2 seed2 depth2 frontier2 table2 found
    hb1 hs1 hf1 hm1 ht1 hb2 hs2 hf2 hm2 ht2 hl
  let s1 : Side body Delta raw param := {
    index := index1, seed := seed1, depth := depth1, frontier := frontier1, table := table1,
    bounded := hb1, subtraction := hs1, front := hf1, member := hm1, tableGraph := ht1 }
  let s2 : Side body Delta raw param := {
    index := index2, seed := seed2, depth := depth2, frontier := frontier2, table := table2,
    bounded := hb2, subtraction := hs2, front := hf2, member := hm2, tableGraph := ht2 }
  exact BindingProof.atRawApply raw param index1 seed1 depth1 frontier1 table1 index2 seed2 depth2 frontier2 table2 found
    (allRaw raw) (packFields s1 s2 found hl)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.Proof
