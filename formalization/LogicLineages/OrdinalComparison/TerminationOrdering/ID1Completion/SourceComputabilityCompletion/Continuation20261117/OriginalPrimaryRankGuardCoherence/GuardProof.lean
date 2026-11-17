module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBranchAdequacy.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.GuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andLeft andRight sameAccept)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (symm)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem keep (source R : Program 2) (window : Program 1) (seed parameter out : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 R out seed parameter)))
    (hs : Nonempty (Derivation body Delta (graph2 (OriginalRankGuardedRepresentative.sameRank R) (suc z) seed parameter))) :
    Nonempty (Derivation body Delta (graph2 (OriginalRankGuardedRepresentative.representative source R window) out seed parameter)) := by
  have hi := InternalAcceptanceBranchProof.successorBranchIntro
    (OriginalRankGuardedRepresentative.sameRank R) (.projection 0) R out z ![seed,parameter] hs hr
  exact HeadWindowBranchAdequacy.SupportProof.branchBoth
    (OriginalRankGuardedRepresentative.active source window) R
    (InternalAcceptance.branch (OriginalRankGuardedRepresentative.sameRank R) (.projection 0) R)
    out ![seed,parameter] hr hi

theorem output (source R : Program 2) (window : Program 1) (seed parameter minimumOut guardedOut : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 R minimumOut seed parameter)))
    (hs : Nonempty (Derivation body Delta (graph2 (OriginalRankGuardedRepresentative.sameRank R) (suc z) seed parameter)))
    (hg : Nonempty (Derivation body Delta (graph2 (OriginalRankGuardedRepresentative.representative source R window) guardedOut seed parameter))) :
    Nonempty (Derivation body Delta (eqn guardedOut minimumOut)) :=
  valueUnique (OriginalRankGuardedRepresentative.representative source R window)
    guardedOut minimumOut ![seed,parameter] hg (keep source R window seed parameter minimumOut hr hs)

theorem sameRank (R : Program 2) (seed parameter minimumOut seedRank minimumRank : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 R minimumOut seed parameter)))
    (hs : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw seedRank seed)))
    (hm : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw minimumRank minimumOut)))
    (he : Nonempty (Derivation body Delta (eqn seedRank minimumRank))) :
    Nonempty (Derivation body Delta (graph2 (OriginalRankGuardedRepresentative.sameRank R) (suc z) seed parameter)) := by
  obtain ⟨he⟩ := he
  have hm' := outputTransport OriginalRawSyntaxTransport.variableRankPackedRaw minimumRank seedRank
    (Fin.cons minimumOut Fin.elim0) ⟨symm he⟩ hm
  exact sameAccept
    (.composition OriginalRawSyntaxTransport.variableRankPackedRaw (fun _ : Fin 1 => R))
    (.composition OriginalRawSyntaxTransport.variableRankPackedRaw (fun _ : Fin 1 => .projection 0))
    seedRank ![seed,parameter]
    (unaryValue OriginalRawSyntaxTransport.variableRankPackedRaw R seedRank minimumOut ![seed,parameter] hm' hr)
    (unaryValue OriginalRawSyntaxTransport.variableRankPackedRaw (.projection 0) seedRank seed ![seed,parameter]
      hs (projectionValue 0 ![seed,parameter]))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.GuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.GuardProof
