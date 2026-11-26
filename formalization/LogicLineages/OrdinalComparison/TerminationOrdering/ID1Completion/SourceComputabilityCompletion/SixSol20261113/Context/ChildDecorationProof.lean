module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowScanCellProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationChildBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildDecorationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeel (graph5)
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryAnnotatedExpansion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph annotation decorate

theorem zeroBelowTwo : Nonempty (Derivation body Delta
    (InternalOriginalOrderSyntaxProof.ltF (z : OTerm alpha) (numeral 2))) := by
  apply InternalOriginalOrderProof.actualOriginalOrderIntroduction body alpha Delta z (numeral 2) (numeral 1)
  rw [InternalSourceInversionSupportProof.onEquality]
  exact ⟨InternalAdditionLawsProof.leftZero (numeral 2)⟩

theorem oneBelowTwo : Nonempty (Derivation body Delta
    (InternalOriginalOrderSyntaxProof.ltF (numeral 1 : OTerm alpha) (numeral 2))) := by
  apply InternalOriginalOrderProof.actualOriginalOrderIntroduction body alpha Delta (numeral 1) (numeral 2) z
  rw [InternalSourceInversionSupportProof.onEquality]
  exact ⟨InternalTagArithmeticSupportProof.trans (InternalTagArithmeticSupportProof.addSucc (numeral 1) z)
    (InternalTagArithmeticSupportProof.congSuc (InternalTagArithmeticSupportProof.addZero (numeral 1)))⟩

theorem decorateValue (index role typ raw rawCell annotated ann outRole outType typed : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph4 annotation ann index role typ raw)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ann outRole outType)))
    (htp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed outType rawCell)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing annotated outRole typed))) :
    Nonempty (Derivation body Delta (graph5 decorate annotated index role typ raw rawCell)) := by
  let xs : Fin 5 → OTerm alpha := ![index,role,typ,raw,rawCell]
  let a : Program 5 := .composition annotation ![.projection 0,.projection 1,.projection 2,.projection 3]
  have av : Nonempty (Derivation body Delta (programGraph a ann xs)) := by
    apply compositionValue annotation ![.projection 0,.projection 1,.projection 2,.projection 3]
      ann xs (Fin.cons index (Fin.cons role (Fin.cons typ (Fin.cons raw Fin.elim0)))) ha
    intro i
    exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
      (Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs) (fun k => Fin.elim0 k)))) i
  have leftValue := unaryValue InternalUnpair.left a outRole ann xs (pairLeft ann outRole outType hap) av
  have rightValue := unaryValue InternalUnpair.right a outType ann xs (pairRight ann outRole outType hap) av
  have typedValue := binaryValue InternalPairing.pairing (rightOf a) (.projection 4)
    typed outType rawCell xs htp rightValue (projectionValue 4 xs)
  rw [graph5,decorate]
  exact binaryValue InternalPairing.pairing (leftOf a) (pairOf (rightOf a) (.projection 4))
    annotated outRole typed xs hn leftValue typedValue
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildDecorationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildDecorationProof
