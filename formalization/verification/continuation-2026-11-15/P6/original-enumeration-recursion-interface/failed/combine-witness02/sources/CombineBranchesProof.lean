module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.PositiveCombineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsCacheCoherence.DomainSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.CombineBranchesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open CombineFrameProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem forward (n : Nat) (x : Frame body Delta) (out : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph3 (G n) out x.node x.answers x.param))) :
    Nonempty (Derivation body Delta (relation n x out)) := by
  apply zeroSuccessorCases Delta x.f _
  · let A := eqn x.f z
    have he : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hf := outputTransport fuel x.f z ![x.node,x.answers,x.param] he (withHyp (fuelGraph x) A)
    have hv := CombineScalarProof.zeroValue n x.node x.answers x.param hf
    have heo := valueUnique (G n) out (numeral 1) ![x.node,x.answers,x.param] (withHyp ho A) hv
    obtain ⟨ha⟩ := andIntro he heo
    exact ⟨InternalQuotientComparisonProof.orLeft ha⟩
  · intro beta j Theta k hj he
    rw [relationRename n x out j Theta hj]
    let y := x.rename j Theta hj
    have hf := outputTransport fuel y.f (suc k) ![y.node,y.answers,y.param] he (fuelGraph y)
    have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
    rw [graph3Rename] at hoj
    have hw := PositiveCombineProof.witnesses n y k (out.relabel j) hf hoj
    have hn := OriginalCodeBoundsCacheCoherence.DomainSupportProof.unequalZero y.f k he
    obtain ⟨ha⟩ := andIntro hn hw
    exact ⟨InternalQuotientComparisonProof.orRight ha⟩

theorem witnessBackward (n : Nat) (x : Frame body Delta) (k out : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph3 fuel (suc k) x.node x.answers x.param)))
    (hw : Nonempty (Derivation body Delta (Targets.positiveOutput n out x.answers x.ts x.hs x.ls x.tb x.vb))) :
    Nonempty (Derivation body Delta (graph3 (G n) out x.node x.answers x.param)) := by
  apply InternalFiniteBlocksProof.elimination body alpha 3 Delta
    (CombineWitnessProof.matrix n out x.answers x.ts x.hs x.ls x.tb x.vb) _ hw
  let j : alpha → alpha ⊕ Fin 3 := Sum.inl
  let ys : Fin 3 → OTerm (alpha ⊕ Fin 3) := fun i => .var (.inr i)
  let Theta := CombineWitnessProof.matrix n out x.answers x.ts x.hs x.ls x.tb x.vb ::
    Delta.map (fun q => q.relabel j)
  have hj : ∀ q ∈ Delta, q.relabel j ∈ Theta := by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  let y := x.rename j Theta hj
  have hm : Nonempty (Derivation body Theta
      (CombineWitnessProof.matrix n out x.answers x.ts x.hs x.ls x.tb x.vb)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hfj := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  simp only [graph3Rename,InternalTagArithmeticSyntaxProof.sucRelabel] at hfj
  rw [graph3Rename]
  exact PositiveCombineProof.atFields n y (k.relabel j) (out.relabel j) (ys 0) (ys 1) (ys 2) hfj hm

theorem nonzeroBackward (n : Nat) (x : Frame body Delta) (out : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (eqn x.f z).not))
    (hw : Nonempty (Derivation body Delta (Targets.positiveOutput n out x.answers x.ts x.hs x.ls x.tb x.vb))) :
    Nonempty (Derivation body Delta (graph3 (G n) out x.node x.answers x.param)) := by
  apply zeroSuccessorCases Delta x.f _
  · obtain ⟨hn⟩ := withHyp hn (eqn x.f z)
    exact ⟨Derivation.explosion (Derivation.implicationElimination hn (Derivation.hypothesis List.mem_cons_self))⟩
  · intro beta j Theta k hj he
    rw [graph3Rename]
    let y := x.rename j Theta hj
    have hf := outputTransport fuel y.f (suc k) ![y.node,y.answers,y.param] he (fuelGraph y)
    have hwj := InternalGraphCompositionFunctionalityProof.renameInto hw j Theta hj
    rw [CombineWitnessProof.positiveRename] at hwj
    exact witnessBackward n y k (out.relabel j) hf hwj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.CombineBranchesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.CombineBranchesProof
