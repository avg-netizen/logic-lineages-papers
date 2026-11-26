module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.NumberedBoundsCongruenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.UnaryExchangeAtProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.HeadMoveBoundsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.NumberedGuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.NumberedMoveAtProof
open Continuation20261114 Continuation20261115 Continuation20261116
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open ExchangeInduction ExchangeInductionBindingProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (symm)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open Continuation20261115
open OriginalRawSyntaxTransport (numberedConstructor)

theorem atValues (n : Nat) (arity : Fin n → Nat)
    (left right label lh rh lt rt lts rts lc ld rc rd symbols types cv dv other lv rv : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,lh,lt,lc,lts,ld])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,rh,rt,rc,rts,rd])))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)))
    (hm : Nonempty (Derivation body Delta (programGraph (Continuation20261114.OriginalHeadMove.headMove n arity) (suc z) ![lh,lc,rh,rc,symbols,types])))
    (he : Nonempty (Derivation body Delta (eqn ld rd)))
    (hcv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw cv lc)))
    (hdv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw dv rc)))
    (hlo : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw other ld)))
    (hlv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw lv left)))
    (hrv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw rv right))) :
    Nonempty (Derivation body Delta (eqn lv rv)) := by
  have hleft := Continuation20261116.OriginalExchangeBoundsPreservation.NumberedGuardProof.children n left label lh lt lc lts ld hlc hlg
  have hright := Continuation20261116.OriginalExchangeBoundsPreservation.NumberedGuardProof.children n right label rh rt rc rts rd hrc hrg
  obtain ⟨heq⟩ := HeadMoveBoundsProof.preserved n arity lh lc rh rc symbols types cv dv hm
    (andLeft hleft) (andLeft hright) hcv hdv
  have hdv' := outputTransport OriginalRawSyntaxTransport.variableRankRaw dv cv ![rc] ⟨symm heq⟩ hdv
  have hro := headTransport OriginalRawSyntaxTransport.variableRankRaw other ld rd
    (fun i : Fin 0 => Fin.elim0 i) he hlo
  exact NumberedBoundsCongruenceProof.sameChildValues n left right label lh rh lt rt lts rts lc ld rc rd cv other lv rv
    hlc hrc hlg hrg hcv hdv' hlo hro hlv hrv
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.NumberedMoveAtProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.NumberedMoveAtProof
