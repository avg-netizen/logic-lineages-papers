module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierCapacity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.FrontierCapacity.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.BoundProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierCapacity.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (suc sucRelabel eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalGraphCompositionFunctionalityProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem frontierValue (R D : Program 2) (index previous seed param rank depth out : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 R rank seed param)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index rank)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList D) out depth seed param))) :
    Nonempty (Derivation body Delta (programGraph (ExchangeGraphRecursion.frontier R D) out ![index,previous,seed,param])) := by
  let xs : Fin 4 → OTerm alpha := ![index,previous,seed,param]
  have hr' := binaryValue R (.projection 2) (.projection 3) rank seed param xs hr (projectionValue 2 xs) (projectionValue 3 xs)
  have hd' := binaryValue InternalEqualityTest.subtract (.projection 0) (ExchangeGraphRecursion.rank R)
    depth index rank xs hd (projectionValue 0 xs) hr'
  exact InternalOriginalUniformVertexPathSupportProof.ternaryValue (ExchangeFrontier.bindList D)
    (ExchangeGraphRecursion.remaining R) (.projection 2) (.projection 3) out depth seed param xs hf hd' (projectionValue 2 xs) (projectionValue 3 xs)

theorem frontierRecover (R D : Program 2) (index previous seed param rank depth out : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 R rank seed param)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index rank)))
    (hf : Nonempty (Derivation body Delta (programGraph (ExchangeGraphRecursion.frontier R D) out ![index,previous,seed,param]))) :
    Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList D) out depth seed param)) := by
  apply programCases (ExchangeFrontier.bindList D) (Fin.cons depth (Fin.cons seed (Fin.cons param Fin.elim0))) _
  intro beta j Theta value hj hv
  rw [graph3Rename]
  simp only [consTermRename,emptyRename] at hv
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  rw [graph2Rename] at hrj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  rw [graph2Rename] at hdj
  have hfj := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  rw [InternalControlGraphSupportProof.programRename] at hfj
  have hx : (fun i => (![index,previous,seed,param] i).relabel j) = ![index.relabel j,previous.relabel j,seed.relabel j,param.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hfj
  have hnew := frontierValue R D (index.relabel j) (previous.relabel j) (seed.relabel j) (param.relabel j) (rank.relabel j) (depth.relabel j) value hrj hdj hv
  have he := valueUnique (ExchangeGraphRecursion.frontier R D) value (out.relabel j) _ hnew hfj
  exact outputTransport (ExchangeFrontier.bindList D) value (out.relabel j) ![depth.relabel j,seed.relabel j,param.relabel j] he hv

theorem capacityAt (n : Nat) (index seed param depth frontier node seedRank nodeRank : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) seedRank seed param)))
    (hb : Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index seedRank)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index seedRank)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList (OriginalDecodedDependencies.dependencies n)) frontier depth seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)))
    (hc : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) nodeRank node param))) :
    Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded nodeRank index)) := by
  obtain ⟨he⟩ := SubtractionAlignment.Proof.complement body alpha Delta index seedRank depth hb hs
  have hbound := OriginalDecodedFrontierRank.BoundProof.rankBound n body alpha Delta depth seed param frontier node seedRank nodeRank hr hf hm hc
  have ht := PrimaryUncoveredCount.OrderProof.transport (OrdinaryArithmetic.addTerm depth nodeRank) seedRank
    (OrdinaryArithmetic.addTerm depth nodeRank) (OrdinaryArithmetic.addTerm depth index)
    ⟨InternalTagArithmeticSupportProof.refl _⟩
    ⟨InternalTagArithmeticSupportProof.trans (InternalTagArithmeticSupportProof.symm he) (InternalAdditionLawsProof.commutativity index depth)⟩ hbound
  exact FrontierCapacity.Proof.boundedCancel depth nodeRank index ht

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierCapacity.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierCapacity.SupportProof
