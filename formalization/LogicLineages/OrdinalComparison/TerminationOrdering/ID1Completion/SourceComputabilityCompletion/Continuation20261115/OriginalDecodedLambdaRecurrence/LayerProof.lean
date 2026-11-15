module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.GuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledStructuralFields.LambdaProof
public import Mathlib.Tactic.FinCases
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.LayerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
/-- Actual slot17/18 overrides moved into unused structural supplier positions.
This is an AST identity, not a calibrated filler hypothesis. -/
def filled (n : Nat) (arity : Fin n → Nat) (V : Program 3) (i : Fin 19) : Program 3 :=
  if i = 17 then HeadResultFields.result V false else
  if i = 18 then HeadResultFields.result V true else
    HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun j => Fin.elim0 j)) V i

theorem layerIdentity (n : Nat) (arity : Fin n → Nat) (V : Program 3) :
    ConcreteHeadMoveLayer.layer n arity V = StructuralExchangeFields.layer (filled n arity V) V := by
  apply congrArg (fun U => TransparentExchangeLayer.optional U V)
  funext i
  fin_cases i <;> rfl

theorem lambda (n : Nat) (arity : Fin n → Nat) (node code param source target sigma tau q r head tail : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node code param)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hs : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor source sigma q)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor target tau r)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail))) :
    (Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.layer n arity) (numeral 2) node code param)) ↔
     Nonempty (Derivation body Delta (eqn sigma tau ⊓ eqn head (numeral 1)))) := by
  unfold OriginalDecodedLayerCalibration.layer
  rw [layerIdentity]
  exact InstalledStructuralFields.LambdaProof.internalLambda (filled n arity (OriginalDecodedLayerCalibration.guard n))
    (OriginalDecodedLayerCalibration.guard n) body alpha Delta node code param source target sigma tau q r head tail hg hn hs ht hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.LayerProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.LayerProof
