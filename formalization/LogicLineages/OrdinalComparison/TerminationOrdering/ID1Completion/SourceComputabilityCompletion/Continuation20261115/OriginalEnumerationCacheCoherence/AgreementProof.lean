module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.FrameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.AgreementBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.AgreementProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114 SideProof FrameProof
open OriginalMapGraphTransport.Targets OriginalMapGraphTransport.AgreementSyntaxProof
open OriginalMapGraphTransport.AgreementBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
variable {n : Nat}
attribute [local irreducible] programGraph
theorem childTransport {raw param : OTerm alpha} (f : Frame n body Delta raw param)
    (budget deps child found : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw n budget)))
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R budget raw param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.D deps raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found f.old1 child))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found f.old2 child)) := by
  apply programCases OriginalEnumerationRecursionInterface.R (Fin.cons child (Fin.cons param Fin.elim0)) _
  intro beta j Theta rank hj hc
  simp only [consTermRename,emptyRename] at hc
  rw [graph2Rename]
  let fn := f.rename j Theta hj
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  rw [graph2Rename] at hrj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  rw [graph2Rename] at hdj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  rw [graph2Rename] at hlj
  exact childTransportAt fn (budget.relabel j) (deps.relabel j) (child.relabel j) rank (found.relabel j) ihj hrj hdj hmj hc hlj

theorem agreement {raw param : OTerm alpha} (f : Frame n body Delta raw param)
    (budget deps : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw n budget)))
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R budget raw param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.D deps raw param))) :
    Nonempty (Derivation body Delta (lookupAgreement deps f.old1 f.old2)) := by
  apply agreementIntro
  let j : alpha → alpha ⊕ Fin 2 := Sum.inl
  let key : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
  let value : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
  let M := graph2 contains (numeral 1) (deps.relabel j) key
  let L := graph2 ExchangeMapGraph.lookup value (f.old1.relabel j) key
  let C := L :: M :: Delta.map (fun q => q.relabel j)
  have hj : ∀ q ∈ Delta, q.relabel j ∈ C := by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  let fn := f.rename j C hj
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j C hj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j C hj
  rw [graph2Rename] at hrj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j C hj
  rw [graph2Rename] at hdj
  have hm : Nonempty (Derivation body C M) := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hl : Nonempty (Derivation body C L) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := childTransport fn (budget.relabel j) (deps.relabel j) key value ihj hrj hdj hm hl
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.AgreementProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.AgreementProof
