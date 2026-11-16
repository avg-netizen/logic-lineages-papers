module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.InputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.SelectorsProof
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

theorem lengthRecover (seed param gamma count : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.gamma gamma seed param)))
    (hb : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.bound count seed param))) :
    Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count gamma)) :=
  unaryRecover OriginalContextInsertion.length OriginalClassCodes.gamma count gamma ![seed,param] hb hg

theorem fuelValue (n : Nat) (seed param size : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.size n) size seed param))) :
    Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.fuel n) (add size size) seed param)) :=
  binaryValue InternalArithmeticPrograms.addition (OriginalClassCodes.size n) (OriginalClassCodes.size n)
    (add size size) size size ![seed,param] (InternalArithmeticProgramsSupportProof.additionValue size size) hs hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.SelectorsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.SelectorsProof
