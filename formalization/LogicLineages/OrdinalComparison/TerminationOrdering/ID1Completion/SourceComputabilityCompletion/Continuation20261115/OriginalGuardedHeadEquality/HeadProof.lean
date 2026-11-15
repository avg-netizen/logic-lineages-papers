module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.FieldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.ClauseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.HeadProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem constructorRename {beta : Type} (numbered : Bool) (raw k f tau base ts extras : OTerm alpha) (j : alpha → beta) :
    (Targets.constructor numbered raw k f tau base ts extras).relabel j =
      Targets.constructor numbered (raw.relabel j) (k.relabel j) (f.relabel j) (tau.relabel j) (base.relabel j) (ts.relabel j) (extras.relabel j) := by
  cases numbered with
  | false => exact graph2Rename ordinaryConstructor raw f base j
  | true => exact ConcreteHeadMoveLayer.SyntaxProof.sixRename numberedConstructor raw k f tau base ts extras j

theorem atFields (n : Nat) (numbered : Bool) (raw k f tau base ts extras payload first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (Targets.constructor numbered raw k f tau base ts extras)))
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload raw)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first raw)))
    (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second raw))) :
    Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) f)) := by
  have ht := FieldProof.tagValue numbered raw k f tau base ts extras hc
  have hleft := unaryRecover InternalUnpair.left (.projection 0)
    (numeral (if numbered then 5 else 4)) raw ![raw] ht (projectionValue 0 ![raw])
  have hpair := InternalApplicationCertificateConstructorsSupportProof.reconstructPair
    raw (numeral (if numbered then 5 else 4)) payload hleft hp
  have hh := FieldProof.headValue numbered raw k f tau base ts extras hc
  have ha := (OriginalCodeValidityConstructors.Proof.guardConstructors n body alpha Delta
    raw (numeral (if numbered then 5 else 4)) payload first second f hpair hf hs hh).mp hv
  exact ClauseProof.headFromAllowed n numbered payload first second f ha

theorem headAccepted (n : Nat) (numbered : Bool) (raw k f tau base ts extras : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (Targets.constructor numbered raw k f tau base ts extras)))
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw))) :
    Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) f)) := by
  let qs : Fin 3 → Program 1 := ![InternalUnpair.right,firstOf (.projection 0),secondOf (.projection 0)]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs (Fin.cons raw Fin.elim0) _
  intro beta j ys Theta hj hq
  simp only [consTermRename,emptyRename] at hq
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  rw [constructorRename] at hcj
  have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hvj
  exact atFields n numbered (raw.relabel j) (k.relabel j) (f.relabel j) (tau.relabel j)
    (base.relabel j) (ts.relabel j) (extras.relabel j) (ys 0) (ys 1) (ys 2) hcj hvj (hq 0) (hq 1) (hq 2)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.HeadProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.HeadProof
