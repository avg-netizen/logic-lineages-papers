module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.BinaryChildrenQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ConsProof
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
theorem preserved (n : Nat) (arity : Fin n → Nat)
 (left right lm rm lc ld rc rd node window context symbols types : OTerm alpha)
 (hlc : Nonempty (Derivation body Delta (graph3 consConstructor left lm lc ld)))
 (hrc : Nonempty (Derivation body Delta (graph3 consConstructor right rm rc rd)))
 (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
 (hedge : Nonempty (Derivation body Delta (edge n arity left right node window)))
 (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
 Nonempty (Derivation body Delta (PlainAwareStructuralDefinitions.Transfer n arity
  (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
  true left right context)) :=
 BinaryChildrenQueryProof.preserved true n arity left right lm rm lc ld rc rd node window context symbols types
  hlc hrc henv hedge ih

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ConsProof
