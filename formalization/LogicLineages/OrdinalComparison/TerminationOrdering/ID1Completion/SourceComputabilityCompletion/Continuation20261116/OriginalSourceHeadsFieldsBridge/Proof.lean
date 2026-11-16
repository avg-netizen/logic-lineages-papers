module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceHeadsFieldsBridge.WitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceHeadsFieldsBridge.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalEncodedNumberedEnumerationBranch.MapImageProof (image imageRename)
open GuardedSourceSyntaxProof (numeralRename)

def queries (n : Nat) (arity : Fin n → Nat) : Fin 2 → Program 3 :=
  ![.composition (OriginalSourceHeads.sourceHeads n arity) ![.projection 1,.projection 2],
    .composition OriginalHeadEncodingBridge.encodeHead (fun _ : Fin 1 => .projection 0)]

theorem internalHeadAllowed : Targets.InternalHeadAllowed := by
  intro n arity body alpha Delta seed param rawHead symbols types heads hsy hty hh hsource
  change Nonempty (Derivation body Delta (image (OriginalEncodedHeadConversion.convert n) heads rawHead))
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (queries n arity) ![rawHead,symbols,types] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![rawHead,symbols,types] i).relabel j) =
      ![rawHead.relabel j,symbols.relabel j,types.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  rw [imageRename]
  let xs : Fin 3 → OTerm beta := ![rawHead.relabel j,symbols.relabel j,types.relabel j]
  have hraw := binaryRecover (OriginalSourceHeads.sourceHeads n arity) (.projection 1) (.projection 2)
    (ys 0) (symbols.relabel j) (types.relabel j) xs (hq 0) (projectionValue 1 xs) (projectionValue 2 xs)
  have hencoded := unaryRecover OriginalHeadEncodingBridge.encodeHead (.projection 0)
    (ys 1) (rawHead.relabel j) xs (hq 1) (projectionValue 0 xs)
  have hsyj := renameInto hsy j Theta hj
  have htyj := renameInto hty j Theta hj
  have hhj := renameInto hh j Theta hj
  have hsj := renameInto hsource j Theta hj
  simp only [graph2Rename] at hsyj htyj hhj
  simp only [OriginalGuardedHeadSourceCoverage.Targets.sourceHead,
    InternalRecursionGraphStepSyntaxProof.conjunctionRename,graph1Rename,graph3Rename,numeralRename] at hsj
  have hmember := CompositionProof.rawMember n arity (rawHead.relabel j) (symbols.relabel j) (types.relabel j)
    (ys 0) hraw (andRight hsj)
  have hmap := CompositionProof.mapped n arity (seed.relabel j) (param.relabel j) (symbols.relabel j)
    (types.relabel j) (ys 0) (heads.relabel j) hsyj htyj hraw hhj
  exact WitnessProof.introduce n (rawHead.relabel j) (ys 0) (heads.relabel j) (ys 1)
    (andLeft hsj) hmember hmap hencoded

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceHeadsFieldsBridge.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceHeadsFieldsBridge.Proof
