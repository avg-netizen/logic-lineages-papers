module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.BranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.SourceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Continuation20261114 Continuation20261115
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof (orCases)
open GuardedSourceSyntaxProof (numeralRename)
open WindowSourceHeadInclusion.ClosureSyntaxProof (closureRename)

theorem atPair (n : Nat) (arity : Fin n → Nat) (raw tag payload symbols types : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) raw)))
    (hw : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) (numeral 1) raw symbols types)))
    (hc : Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed types))) :
    Nonempty (Derivation body Delta (graph3 (OriginalSourceHeads.member n arity) (numeral 1) raw symbols types)) := by
  have ha := (OriginalHeadDecoderValidity.Proof.internalAcceptedBranches n body alpha Delta raw tag payload hp).mp hv
  apply orCases ha
  · intro Theta inc hb
    exact BranchProof.basic n arity raw tag payload symbols types (weakenProof hp inc) (weakenProof hw inc) hb
  · intro Theta inc rest
    apply orCases rest
    · intro Xi ix h2
      exact BranchProof.unary n arity 0 raw tag payload symbols types
        (weakenProof hp (fun p h => ix p (inc p h))) (weakenProof hw (fun p h => ix p (inc p h)))
        (weakenProof hc (fun p h => ix p (inc p h))) h2
    · intro Xi ix rest2
      apply orCases rest2
      · intro Zeta iz h3
        exact BranchProof.unary n arity 1 raw tag payload symbols types
          (weakenProof hp (fun p h => iz p (ix p (inc p h)))) (weakenProof hw (fun p h => iz p (ix p (inc p h))))
          (weakenProof hc (fun p h => iz p (ix p (inc p h)))) h3
      · intro Zeta iz rest3
        apply orCases rest3
        · intro Eta ie h4
          exact BranchProof.application n arity raw tag payload symbols types
            (weakenProof hp (fun p h => ie p (iz p (ix p (inc p h)))))
            (weakenProof hw (fun p h => ie p (iz p (ix p (inc p h))))) h4
        · intro Eta ie h5
          exact BranchProof.ranked n arity raw tag payload symbols types
            (weakenProof hp (fun p h => ie p (iz p (ix p (inc p h)))))
            (weakenProof hw (fun p h => ie p (iz p (ix p (inc p h))))) (andLeft h5)

theorem source (n : Nat) (arity : Fin n → Nat) (raw symbols types : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) raw)))
    (hw : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) (numeral 1) raw symbols types)))
    (hc : Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed types))) :
    Nonempty (Derivation body Delta (Targets.sourceHead n arity raw symbols types)) := by
  apply OriginalDecodedRank.SupportProof.pairCases raw _
  intro beta j Theta tag payload hj hp
  simp only [Targets.sourceHead,InternalRecursionGraphStepSyntaxProof.conjunctionRename,graph1Rename,graph3Rename,numeralRename]
  have hvj := renameInto hv j Theta hj
  have hwj := renameInto hw j Theta hj
  have hcj := renameInto hc j Theta hj
  simp only [graph1Rename,graph3Rename,numeralRename,closureRename] at hvj hwj hcj
  exact andIntro hvj (atPair n arity (raw.relabel j) tag payload (symbols.relabel j) (types.relabel j) hp hvj hwj hcj)

theorem guarded (n : Nat) (arity : Fin n → Nat) (head context symbols types : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (graph2 (window n arity) (numeral 1) head context)))
    (hs : Nonempty (Derivation body Delta (graph1 contextSymbols symbols context)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalUniverseDomainCoverage.contextTypes types context)))
    (hc : Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed types))) :
    Nonempty (Derivation body Delta (Targets.sourceHead n arity head symbols types)) := by
  have hh := GuardProof.recover n arity head context symbols types hw hs ht
  exact source n arity head symbols types (andLeft hh) (andRight hh) hc

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.SourceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.SourceProof
