module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedNumberedRecurrence.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedAtChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.OrdinaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSupportProof (refl)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open Continuation20261115
open OriginalRawSyntaxTransport Induction
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InductionSyntaxProof MatrixSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
theorem atValues (n : Nat) (arity : Fin n → Nat)
    (left right k l f g tau upsilon base dest ts us extras otherExtras node typ gamma window context symbols types : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![k,f,tau,base,ts,extras])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![l,g,upsilon,dest,us,otherExtras])))
    (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
    (hedge : Nonempty (Derivation body Delta (edge n arity left right node window)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left)))
    (ha : Nonempty (Derivation body Delta (accepted n arity false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (plain n arity false typ right gamma))) :
    Nonempty (Derivation body Delta (accepted n arity false typ right gamma context)) := by
  let queries : Fin 2 → Program 4 := ![pairOf (.projection 0) (.projection 1),pairOf (.projection 2) (.projection 3)]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases queries ![base,dest,extras,otherExtras] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![base,dest,extras,otherExtras] i).relabel j) =
      ![base.relabel j,dest.relabel j,extras.relabel j,otherExtras.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  let xs := ![base.relabel j,dest.relabel j,extras.relabel j,otherExtras.relabel j]
  have hfirst := InternalApplicationCertificateConstructorsSupportProof.binaryRecover InternalPairing.pairing (.projection 0) (.projection 1)
    (ys 0) (base.relabel j) (dest.relabel j) xs (hq 0) (projectionValue 0 xs) (projectionValue 1 xs)
  have hlast := InternalApplicationCertificateConstructorsSupportProof.binaryRecover InternalPairing.pairing (.projection 2) (.projection 3)
    (ys 1) (extras.relabel j) (otherExtras.relabel j) xs (hq 1) (projectionValue 2 xs) (projectionValue 3 xs)
  rw [acceptedRename]
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have henv' := renameInto henv j Theta hj
  have hedge' := renameInto hedge j Theta hj
  have ih' := renameInto ih j Theta hj
  have ha' := renameInto ha j Theta hj
  have hp' := renameInto hp j Theta hj
  simp only [programRename,OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename] at hlc' hrc'
  rw [environmentRename] at henv'
  rw [edgeRename] at hedge'
  rw [belowRawRename] at ih'
  rw [acceptedRename] at ha'
  rw [plainRename] at hp'
  exact NumberedAtChildrenProof.atChildren n arity (left.relabel j) (right.relabel j)
    (k.relabel j) (l.relabel j) (f.relabel j) (g.relabel j) (tau.relabel j) (upsilon.relabel j)
    (base.relabel j) (dest.relabel j) (ts.relabel j) (us.relabel j) (extras.relabel j) (otherExtras.relabel j)
    (node.relabel j) (ys 0) (ys 1) (typ.relabel j) (gamma.relabel j) (window.relabel j)
    (context.relabel j) (symbols.relabel j) (types.relabel j)
    hlc' hrc' hfirst hlast henv' hedge' ih' ha' hp'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedProof
