module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineNonBottomMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.PositiveSpineRulesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineNonBottomProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem contradictionAtValues (source target certificate parameter typ tm td : OTerm α)
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typ source)))
    (hm : Nonempty (Derivation body Gamma (BottomSpineMeasure.graph tm target)))
    (hd : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right td tm)))
    (hb : Nonempty (Derivation body Gamma (BottomRepresentative.bottomGraph (suc z) source)))
    (hg : Nonempty (Derivation body Gamma
      (OriginalSpineGuardLeaf.spineAccepted source target certificate parameter))) :
    Nonempty (Derivation body Gamma (⊥ : Formula α)) := by
  have hc := BottomSourceShapeProof.bottomRecover source typ hl hb
  have hs := OriginalSpineNonBottomMeasureProof.bottomMeasure source typ hc
  have hp := BottomSourceClosedProof.numeralPair (body := body) (α := α) (Delta := Gamma) 1 0
  have hsf := pairLeft (numeral (Nat.pair 1 0)) (suc z) z hp
  have hsd := pairRight (numeral (Nat.pair 1 0)) (suc z) z hp
  let xs : Fin 4 → OTerm α := Fin.cons source (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  obtain ⟨himp⟩ := PositiveSpineRulesProof.spineRecover BottomSpineMeasure.measure
    (numeral (Nat.pair 1 0)) tm z td xs hs hm hsd hd hg
  obtain ⟨hsf⟩ := hsf
  have hlt := Derivation.conjunctionRight (Derivation.implicationElimination himp hsf)
  obtain ⟨hn⟩ := InternalBoundedDescentNormalizerStepProof.notLessZero (body := body) (Gamma := Gamma) td
  exact ⟨Derivation.implicationElimination hn hlt⟩

theorem contradiction (source target certificate parameter : OTerm α)
    (hb : Nonempty (Derivation body Gamma (BottomRepresentative.bottomGraph (suc z) source)))
    (hg : Nonempty (Derivation body Gamma
      (OriginalSpineGuardLeaf.spineAccepted source target certificate parameter))) :
    Nonempty (Derivation body Gamma (⊥ : Formula α)) := by
  apply programCases InternalUnpair.left (Fin.cons source Fin.elim0) _
  intro β j Delta typ hj hl
  have hb' := renameInto hb j Delta hj
  have hg' := renameInto hg j Delta hj
  simp only [BottomRepresentative.bottomGraph,graph1Rename,sucRelabel,zRelabel] at hb'
  simp only [OriginalSpineGuardLeaf.spineAccepted,graph4Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hg'
  have hl' : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ (source.relabel j))) := by
    simpa only [graph1,consTermRename,emptyRename] using hl
  apply programCases BottomSpineMeasure.measure (Fin.cons (target.relabel j) Fin.elim0) _
  intro χ k Theta tm hk hm
  have hb'' := renameInto hb' k Theta hk
  have hg'' := renameInto hg' k Theta hk
  have hl'' := renameInto hl' k Theta hk
  simp only [graph1Rename,sucRelabel,zRelabel] at hb'' hl''
  simp only [graph4Rename,sucRelabel,zRelabel] at hg''
  have hm' : Nonempty (Derivation body Theta
      (BottomSpineMeasure.graph tm ((target.relabel j).relabel k))) := by
    simpa only [BottomSpineMeasure.graph,graph1,consTermRename,emptyRename] using hm
  apply programCases InternalUnpair.right (Fin.cons tm Fin.elim0) _
  intro δ l Xi td hXi hd
  have hb3 := renameInto hb'' l Xi hXi
  have hg3 := renameInto hg'' l Xi hXi
  have hl3 := renameInto hl'' l Xi hXi
  have hm3 := renameInto hm' l Xi hXi
  simp only [graph1Rename,sucRelabel,zRelabel] at hb3 hl3
  simp only [graph4Rename,sucRelabel,zRelabel] at hg3
  simp only [BottomSpineMeasure.graph,graph1Rename] at hm3
  have hd' : Nonempty (Derivation body Xi (graph1 InternalUnpair.right td (tm.relabel l))) := by
    simpa only [graph1,consTermRename,emptyRename] using hd
  exact contradictionAtValues (((source.relabel j).relabel k).relabel l)
    (((target.relabel j).relabel k).relabel l) (((certificate.relabel j).relabel k).relabel l)
    (((parameter.relabel j).relabel k).relabel l) ((typ.relabel k).relabel l)
    (tm.relabel l) td hl3 hm3 hd' hb3 hg3

theorem actualOriginalSpineGuardRejectsBottom :
    OriginalSpineNonBottomTargets.ActualOriginalSpineGuardRejectsBottom := by
  intro body α Delta source target certificate parameter
  let H := OriginalSpineGuardLeaf.spineAccepted source target certificate parameter
  let B := BottomRepresentative.bottomGraph (suc z) source
  have hh : Nonempty (Derivation body (H :: Delta) H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hb : Nonempty (Derivation body (B :: H :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨result⟩ := contradiction source target certificate parameter hb (withHyp hh B)
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction result)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineNonBottomProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineNonBottomProof
