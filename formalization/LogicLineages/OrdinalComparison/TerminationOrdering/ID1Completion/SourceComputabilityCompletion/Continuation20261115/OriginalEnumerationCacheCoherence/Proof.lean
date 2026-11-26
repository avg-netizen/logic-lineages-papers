module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.CasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 SideProof
open InductionDefinitions InductionSyntaxProof BindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
variable {n : Nat}
attribute [local irreducible] programGraph
theorem rankStep (n : Nat)
    (budget : OTerm alpha) (ih : Nonempty (Derivation body Delta (BelowRaw n budget))) :
    Nonempty (Derivation body Delta (AtRaw n budget)) := by
  apply atRawIntro n budget
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let r : OTerm (alpha ⊕ Fin 15) := budget.relabel Sum.inl
  let node : OTerm (alpha ⊕ Fin 15) := .var (.inr 0)
  let param : OTerm (alpha ⊕ Fin 15) := .var (.inr 1)
  let index1 : OTerm (alpha ⊕ Fin 15) := .var (.inr 2)
  let seed1 : OTerm (alpha ⊕ Fin 15) := .var (.inr 3)
  let rank1 : OTerm (alpha ⊕ Fin 15) := .var (.inr 4)
  let depth1 : OTerm (alpha ⊕ Fin 15) := .var (.inr 5)
  let frontier1 : OTerm (alpha ⊕ Fin 15) := .var (.inr 6)
  let table1 : OTerm (alpha ⊕ Fin 15) := .var (.inr 7)
  let index2 : OTerm (alpha ⊕ Fin 15) := .var (.inr 8)
  let seed2 : OTerm (alpha ⊕ Fin 15) := .var (.inr 9)
  let rank2 : OTerm (alpha ⊕ Fin 15) := .var (.inr 10)
  let depth2 : OTerm (alpha ⊕ Fin 15) := .var (.inr 11)
  let frontier2 : OTerm (alpha ⊕ Fin 15) := .var (.inr 12)
  let table2 : OTerm (alpha ⊕ Fin 15) := .var (.inr 13)
  let found : OTerm (alpha ⊕ Fin 15) := .var (.inr 14)
  let Theta := fields n r node param index1 seed1 rank1 depth1 frontier1 table1 index2 seed2 rank2 depth2 frontier2 table2 found :: Delta.map (fun q => q.relabel Sum.inl)
  change Derivation body Theta (result r node param index1 seed1 rank1 depth1 frontier1 table1 index2 seed2 rank2 depth2 frontier2 table2 found)
  have hf : Nonempty (Derivation body Theta (fields n r node param index1 seed1 rank1 depth1 frontier1 table1 index2 seed2 rank2 depth2 frontier2 table2 found)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h0 := andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (hf)))))))))))))
  have h1 := andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (hf)))))))))))))
  have h2 := andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (hf))))))))))))
  have h3 := andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (hf)))))))))))
  have h4 := andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (hf))))))))))
  have h5 := andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (hf)))))))))
  have h6 := andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (hf))))))))
  have h7 := andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (hf)))))))
  have h8 := andRight (andLeft (andLeft (andLeft (andLeft (andLeft (hf))))))
  have h9 := andRight (andLeft (andLeft (andLeft (andLeft (hf)))))
  have h10 := andRight (andLeft (andLeft (andLeft (hf))))
  have h11 := andRight (andLeft (andLeft (hf)))
  have h12 := andRight (andLeft (hf))
  have h13 := andRight (hf)
  let s1 : Side n body Theta node param := {
    index := index1, seed := seed1, seedRank := rank1, depth := depth1, frontier := frontier1, table := table1,
    rankGraph := h1, bounded := h2, subtraction := h3, front := h4, member := h5, tableGraph := h6 }
  let s2 : Side n body Theta node param := {
    index := index2, seed := seed2, seedRank := rank2, depth := depth2, frontier := frontier2, table := table2,
    rankGraph := h7, bounded := h8, subtraction := h9, front := h10, member := h11, tableGraph := h12 }
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih (Sum.inl : alpha → alpha ⊕ Fin 15) Theta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [belowRawRename] at ihj
  exact Classical.choice (CasesProof.core s1 s2 r found ihj h0 h13)

theorem atRank {raw param : OTerm alpha} (s1 s2 : Side n body Delta raw param)
    (rank found : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R rank raw param)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s1.table raw))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s2.table raw)) := by
  apply atRawApply n rank raw param
    s1.index s1.seed s1.seedRank s1.depth s1.frontier s1.table
    s2.index s2.seed s2.seedRank s2.depth s2.frontier s2.table found
    (rawInduction n rank (fun _ _ r h => rankStep n r h))
  exact andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (hr) s1.rankGraph) s1.bounded) s1.subtraction) s1.front) s1.member) s1.tableGraph) s2.rankGraph) s2.bounded) s2.subtraction) s2.front) s2.member) s2.tableGraph) hl

theorem transportSides {raw param : OTerm alpha} (s1 s2 : Side n body Delta raw param)
    (found : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s1.table raw))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s2.table raw)) := by
  apply programCases OriginalEnumerationRecursionInterface.R (Fin.cons raw (Fin.cons param Fin.elim0)) _
  intro beta j Theta rank hj hr
  simp only [consTermRename,emptyRename] at hr
  rw [graph2Rename]
  let t1 := s1.rename j Theta hj
  let t2 := s2.rename j Theta hj
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  rw [graph2Rename] at hlj
  exact atRank t1 t2 rank (found.relabel j) hr hlj

theorem transport : Targets.InternalTransport := by
  intro n body alpha Delta node param index1 seed1 rank1 depth1 frontier1 table1 index2 seed2 rank2 depth2 frontier2 table2 found
    hr1 hb1 hd1 hf1 hm1 ht1 hr2 hb2 hd2 hf2 hm2 ht2 hl
  let s1 : Side n body Delta node param := {
    index := index1, seed := seed1, seedRank := rank1, depth := depth1, frontier := frontier1, table := table1,
    rankGraph := hr1, bounded := hb1, subtraction := hd1, front := hf1, member := hm1, tableGraph := ht1 }
  let s2 : Side n body Delta node param := {
    index := index2, seed := seed2, seedRank := rank2, depth := depth2, frontier := frontier2, table := table2,
    rankGraph := hr2, bounded := hb2, subtraction := hd2, front := hf2, member := hm2, tableGraph := ht2 }
  exact transportSides s1 s2 found hl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.Proof
