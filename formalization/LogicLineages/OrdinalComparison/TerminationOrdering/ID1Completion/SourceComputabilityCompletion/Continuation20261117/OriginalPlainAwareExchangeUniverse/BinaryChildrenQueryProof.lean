module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.BinaryAtChildrenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.BinaryChildrenQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof (symm refl)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open Continuation20261114 Continuation20261115 Continuation20261116
open OriginalRawSyntaxTransport Induction
open OriginalCodeBoundsConstructors.BinaryRootProof (constructor)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalGraphCompositionFunctionalityProof InternalApplicationCertificateConstructorsSyntaxProof
open InductionSyntaxProof MatrixSyntaxProof
theorem atFirst (cons : Bool) (n : Nat) (arity : Fin n → Nat)
 (left right lm rm lc ld rc rd node first window context symbols types : OTerm alpha)
 (hlc : Nonempty (Derivation body Delta (graph3 (constructor cons) left lm lc ld)))
 (hrc : Nonempty (Derivation body Delta (graph3 (constructor cons) right rm rc rd)))
 (hfirst : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing first lc rc)))
 (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
 (hedge : Nonempty (Derivation body Delta (edge n arity left right node window)))
 (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
 Nonempty (Derivation body Delta (PlainAwareStructuralDefinitions.Transfer n arity
  (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
  cons left right context)) := by
 apply InternalAcceptanceSupportProof.programCases InternalPairing.pairing ![ld,rd] _
 intro beta j Theta child hj hchild
 have hx : (fun i => (![ld,rd] i).relabel j) = ![ld.relabel j,rd.relabel j] := by
  funext i
  fin_cases i <;> rfl
 rw [hx] at hchild
 rw [PlainAwareStructuralSyntaxProof.transferRename]
 have hlc' := renameInto hlc j Theta hj
 have hrc' := renameInto hrc j Theta hj
 have henv' := renameInto henv j Theta hj
 have hedge' := renameInto hedge j Theta hj
 have ih' := renameInto ih j Theta hj
 rw [graph3Rename] at hlc' hrc'
 rw [environmentRename] at henv'
 rw [edgeRename] at hedge'
 rw [belowRawRename] at ih'
 have hfirst' := renameInto hfirst j Theta hj
 rw [graph2Rename] at hfirst'
 exact BinaryAtChildrenProof.atChildren cons n arity (left.relabel j) (right.relabel j)
  (lm.relabel j) (rm.relabel j) (lc.relabel j) (ld.relabel j) (rc.relabel j) (rd.relabel j)
  (node.relabel j) (first.relabel j) child (window.relabel j) (context.relabel j) (symbols.relabel j) (types.relabel j)
  hlc' hrc' hfirst' hchild henv' hedge' ih'

theorem preserved (cons : Bool) (n : Nat) (arity : Fin n → Nat)
 (left right lm rm lc ld rc rd node window context symbols types : OTerm alpha)
 (hlc : Nonempty (Derivation body Delta (graph3 (constructor cons) left lm lc ld)))
 (hrc : Nonempty (Derivation body Delta (graph3 (constructor cons) right rm rc rd)))
 (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
 (hedge : Nonempty (Derivation body Delta (edge n arity left right node window)))
 (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
 Nonempty (Derivation body Delta (PlainAwareStructuralDefinitions.Transfer n arity
  (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
  cons left right context)) := by
 apply InternalAcceptanceSupportProof.programCases InternalPairing.pairing ![lc,rc] _
 intro beta j Theta child hj hchild
 have hx : (fun i => (![lc,rc] i).relabel j) = ![lc.relabel j,rc.relabel j] := by
  funext i
  fin_cases i <;> rfl
 rw [hx] at hchild
 rw [PlainAwareStructuralSyntaxProof.transferRename]
 have hlc' := renameInto hlc j Theta hj
 have hrc' := renameInto hrc j Theta hj
 have henv' := renameInto henv j Theta hj
 have hedge' := renameInto hedge j Theta hj
 have ih' := renameInto ih j Theta hj
 rw [graph3Rename] at hlc' hrc'
 rw [environmentRename] at henv'
 rw [edgeRename] at hedge'
 rw [belowRawRename] at ih'
 exact atFirst cons n arity (left.relabel j) (right.relabel j)
  (lm.relabel j) (rm.relabel j) (lc.relabel j) (ld.relabel j) (rc.relabel j) (rd.relabel j)
  (node.relabel j) child (window.relabel j) (context.relabel j) (symbols.relabel j) (types.relabel j)
  hlc' hrc' hchild henv' hedge' ih'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.BinaryChildrenQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.BinaryChildrenQueryProof
