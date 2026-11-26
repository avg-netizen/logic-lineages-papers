module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.DepthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.SelectorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceCandidatesCoverage.AdmissionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceCandidatesCoverage.AssemblyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAdditionLawsProof (add)
open InternalOriginalOrderSyntaxProof (addRelabel)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atValues (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param context gamma types heads typ seedRaw raw candidate pair size maxLabel seedSize seedLabel out count : OTerm alpha)
    (hcontext : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.context context seed param)))
    (hgamma : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.gamma gamma seed param)))
    (htypes : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.types types seed param)))
    (hheads : Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.heads n arity) heads seed param)))
    (hseedSize : Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.size n) seedSize seed param)))
    (hseedLabel : Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.labels n) seedLabel seed param)))
    (hclosed : Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed types)))
    (hguard : Nonempty (Derivation body Delta (graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 1) context)))
    (hseedPair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing seed typ seedRaw)))
    (hcandidatePair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate typ raw)))
    (hseed : Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.TermAccepted H
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity) typ seedRaw gamma context)))
    (ha : Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.TermAccepted H
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity) typ raw gamma context)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size maxLabel)))
    (hs : Nonempty (Derivation body Delta (InternalLessThan.strictLess size (suc seedSize))))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess maxLabel (suc seedLabel))))
    (hout : Nonempty (Derivation body Delta (graph2 (OriginalCandidates.candidates n arity H) out seed param)))
    (hcount : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.bound count seed param))) :
    Nonempty (Derivation body Delta (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) out candidate)) := by
  have hlength := OriginalSourceEnumerationCoverage.SelectorsProof.lengthRecover seed param gamma count hgamma hcount
  have hfuel := OriginalSourceEnumerationCoverage.SelectorsProof.fuelValue n seed param seedSize hseedSize
  have hfields := OriginalUniverseFieldsCoverage.Proof.internalTermFields n arity H body alpha Delta
    seed param context types heads typ raw gamma count pair size maxLabel seedLabel seedSize
    hcontext htypes hheads hclosed ha hlength hb hp hs hl
  have hdepth := OriginalSourceEnumerationCoverage.DepthProof.sourceDepth n H (OriginalUniverseDomainCoverage.member n)
    (OriginalGuardedHeadSourceCoverage.window n arity) typ raw gamma context pair size maxLabel seedSize ha hb hp hs
  have hadmit := AdmissionProof.admitted n arity H seed param typ seedRaw gamma context hseedPair hcontext hgamma hguard hseed
  have hroot := PackingProof.root seed param typ seedRaw hseedPair
  have hpacked := PackingProof.packed H (OriginalUniverseDomainCoverage.member n)
    (OriginalGuardedHeadSourceCoverage.window n arity) candidate typ raw gamma context hcandidatePair ha
  have hn : Nonempty (Derivation body Delta (eqn (numeral 1) (numeral 0)).not) :=
    ⟨Derivation.implicationIntroduction (sucNeZeroApply (Derivation.hypothesis List.mem_cons_self))⟩
  have hm := OriginalClassCodes.MeaningBindingProof.introduce n arity H seed param candidate
    (![raw,typ,types,heads,seedSize,seedLabel,count,add seedSize seedSize,numeral 1] : Fin 9 → OTerm alpha)
    (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro
      (andIntro (andIntro hroot htypes) hheads) hseedSize) hseedLabel) hcount) hfuel) hadmit) hn)
      hcandidatePair) hfields) hdepth)
  have hr := OriginalCandidates.RetainedBindingProof.introduce H seed param candidate gamma (numeral 1) hgamma hpacked hn
  exact (OriginalCandidates.Proof.internalMembership n arity H body alpha Delta seed param out candidate hout).mpr (andIntro hm hr)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceCandidatesCoverage.AssemblyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceCandidatesCoverage.AssemblyProof
