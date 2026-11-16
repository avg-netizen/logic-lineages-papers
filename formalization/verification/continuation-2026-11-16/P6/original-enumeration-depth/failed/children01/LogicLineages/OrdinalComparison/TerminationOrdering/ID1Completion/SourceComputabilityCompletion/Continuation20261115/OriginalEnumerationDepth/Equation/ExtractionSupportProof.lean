module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.Equation.ExtractionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.LayerProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.Equation.ExtractionSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalRecursionGraphStepSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem transport (n : Nat) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw param index1 seed1 rank1 depth1 frontier1 table1 index2 seed2 rank2 depth2 frontier2 table2 found : OTerm alpha)
    (hr1 : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.rank rank1 seed1 param)))
    (hb1 : Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index1 rank1)))
    (hd1 : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth1 index1 rank1)))
    (hf1 : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationDepth.dependency) frontier1 depth1 seed1 param)))
    (hm1 : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier1 raw)))
    (ht1 : Nonempty (Derivation body Delta (graph3 (OriginalEnumerationDepth.graph n) table1 (suc index1) seed1 param)))
    (hr2 : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.rank rank2 seed2 param)))
    (hb2 : Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index2 rank2)))
    (hd2 : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth2 index2 rank2)))
    (hf2 : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationDepth.dependency) frontier2 depth2 seed2 param)))
    (hm2 : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier2 raw)))
    (ht2 : Nonempty (Derivation body Delta (graph3 (OriginalEnumerationDepth.graph n) table2 (suc index2) seed2 param)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table1 raw))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table2 raw)) := by
  let s1 : OriginalEnumerationDepth.CacheCoherence.SideProof.Side n body Delta raw param :=
    { index := index1, seed := seed1, seedRank := rank1, depth := depth1, frontier := frontier1, table := table1,
      rankGraph := hr1, bounded := hb1, subtraction := hd1, front := hf1, member := hm1, tableGraph := ht1 }
  let s2 : OriginalEnumerationDepth.CacheCoherence.SideProof.Side n body Delta raw param :=
    { index := index2, seed := seed2, seedRank := rank2, depth := depth2, frontier := frontier2, table := table2,
      rankGraph := hr2, bounded := hb2, subtraction := hd2, front := hf2, member := hm2, tableGraph := ht2 }
  exact OriginalEnumerationDepth.CacheCoherence.Proof.transportSides s1 s2 found hl

def relation (n : Nat) (raw param table value : OTerm alpha) : Formula alpha :=
  ((graph2 (ExchangeSelectedRecursor.exchange OriginalEnumerationDepth.rank OriginalEnumerationDepth.dependency (OriginalEnumerationDepth.layer n)) value raw param).imp
    (graph2 ExchangeMapGraph.lookup (suc value) table raw)) ⊓
  ((graph2 ExchangeMapGraph.lookup (suc value) table raw).imp
    (graph2 (ExchangeSelectedRecursor.exchange OriginalEnumerationDepth.rank OriginalEnumerationDepth.dependency (OriginalEnumerationDepth.layer n)) value raw param))

theorem relationRename (n : Nat) {beta : Type} (raw param table value : OTerm alpha) (j : alpha → beta) :
    (relation n raw param table value).relabel j =
      relation n (raw.relabel j) (param.relabel j) (table.relabel j) (value.relabel j) := by
  simp only [relation,conjunctionRename,InternalBetaExtensionSyntaxProof.impRename,graph2Rename,sucRelabel]

theorem tableTransport (old table raw value : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn old table)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) old raw))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) table raw)) := by
  unfold graph2 programGraph at hl ⊢
  apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 Delta
    (OrdinaryArithmetic.graphFormula ExchangeMapGraph.lookup) (suc value) ![old,raw] ![table,raw] _ hl
  intro i
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun q => Fin.elim0 q) k) i
  · rw [InternalSourceInversionSupportProof.onEquality]; exact he
  · rw [InternalSourceInversionSupportProof.onEquality]; exact ⟨refl raw⟩

theorem relationAtValue (n : Nat) (raw param table value inner : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph2 (ExchangeSelectedRecursor.exchange OriginalEnumerationDepth.rank OriginalEnumerationDepth.dependency (OriginalEnumerationDepth.layer n)) inner raw param)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc inner) table raw))) :
    Nonempty (Derivation body Delta (relation n raw param table value)) := by
  apply andIntro
  · have hv : Nonempty (Derivation body (graph2 (ExchangeSelectedRecursor.exchange OriginalEnumerationDepth.rank OriginalEnumerationDepth.dependency (OriginalEnumerationDepth.layer n)) value raw param :: Delta)
        (graph2 (ExchangeSelectedRecursor.exchange OriginalEnumerationDepth.rank OriginalEnumerationDepth.dependency (OriginalEnumerationDepth.layer n)) value raw param)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hq⟩ := valueUnique (ExchangeSelectedRecursor.exchange OriginalEnumerationDepth.rank OriginalEnumerationDepth.dependency (OriginalEnumerationDepth.layer n)) inner value ![raw,param] (withHyp he _) hv
    obtain ⟨hout⟩ := outputTransport ExchangeMapGraph.lookup (suc inner) (suc value) ![table,raw]
      ⟨congSuc hq⟩ (withHyp hl _)
    exact ⟨Derivation.implicationIntroduction hout⟩
  · have hv : Nonempty (Derivation body (graph2 ExchangeMapGraph.lookup (suc value) table raw :: Delta)
        (graph2 ExchangeMapGraph.lookup (suc value) table raw)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hq⟩ := valueUnique ExchangeMapGraph.lookup (suc inner) (suc value) ![table,raw] (withHyp hl _) hv
    obtain ⟨hout⟩ := outputTransport (ExchangeSelectedRecursor.exchange OriginalEnumerationDepth.rank OriginalEnumerationDepth.dependency (OriginalEnumerationDepth.layer n)) inner value ![raw,param]
      ⟨cancelSuc hq⟩ (withHyp he _)
    exact ⟨Derivation.implicationIntroduction hout⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.Equation.ExtractionSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.Equation.ExtractionSupportProof
