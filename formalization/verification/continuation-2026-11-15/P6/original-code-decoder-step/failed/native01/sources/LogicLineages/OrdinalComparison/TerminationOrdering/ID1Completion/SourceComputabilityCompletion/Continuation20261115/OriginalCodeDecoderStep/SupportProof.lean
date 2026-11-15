module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant sameOf)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (sameReject branchNumeralIntro branchNumeralElim)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem sameOneRecover {k : Nat} (q : Program k) (xs : Fin k → OTerm alpha)
    (h : Nonempty (Derivation body Delta (programGraph (sameOf q (constant k 1)) (numeral 1) xs))) :
    Nonempty (Derivation body Delta (programGraph q (numeral 1) xs)) := by
  apply InternalAcceptanceSupportProof.programCases q xs _
  intro beta j Theta value hj hv
  simp only [InternalAcceptanceSupportProof.programRename,GuardedSourceSyntaxProof.numeralRename]
  have hh := InternalGraphCompositionFunctionalityProof.renameInto h j Theta hj
  simp only [InternalAcceptanceSupportProof.programRename,GuardedSourceSyntaxProof.numeralRename] at hh
  have he := InternalEqualityTestProof.equalityOfAcceptance value (numeral 1)
    (binaryRecover InternalEqualityTest.equalityTest q (constant k 1) (numeral 1) value (numeral 1)
      (fun i => (xs i).relabel j) hh hv (constantValue 1 (fun i => (xs i).relabel j)))
  exact outputTransport q value (numeral 1) (fun i => (xs i).relabel j) he hv

theorem childFactor (q : Program 2) (table code child : OTerm alpha)
    (hq : Nonempty (Derivation body Delta (graph2 q child table code))) :
    Nonempty (Derivation body Delta (graph2 (childAt q) (numeral 1) table code)) ↔
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (numeral 1) child table)) := by
  let xs : Fin 2 → OTerm alpha := ![table,code]
  let lookupQ : Program 2 := .composition InternalRawListRecursion.lookup ![q,.projection 0]
  constructor
  · intro h
    have hq1 := sameOneRecover lookupQ xs h
    exact binaryRecover InternalRawListRecursion.lookup q (.projection 0) (numeral 1) child table xs
      hq1 hq (projectionValue 0 xs)
  · intro h
    have hq1 := binaryValue InternalRawListRecursion.lookup q (.projection 0) (numeral 1) child table xs
      h hq (projectionValue 0 xs)
    exact InternalApplicationStepPeelSupportProof.sameAccept lookupQ (constant 2 1) (numeral 1) xs hq1 (constantValue 1 xs)

theorem headFactor (n : Nat) (table code head : OTerm alpha)
    (hh : Nonempty (Derivation body Delta (graph2 headField head table code))) :
    Nonempty (Derivation body Delta (graph2 (headAccepted n) (numeral 1) table code)) ↔
    Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head)) :=
  ⟨fun h => unaryRecover (OriginalHeadDecoderValidity.check n) headField (numeral 1) head ![table,code] h hh,
   fun h => unaryValue (OriginalHeadDecoderValidity.check n) headField (numeral 1) head ![table,code] h hh⟩

theorem bothFactor (table code first second : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 firstField first table code)))
    (hs : Nonempty (Derivation body Delta (graph2 secondField second table code))) :
    Nonempty (Derivation body Delta (graph2 bothChildren (numeral 1) table code)) ↔
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (numeral 1) first table ⊓
      graph2 InternalRawListRecursion.lookup (numeral 1) second table)) := by
  constructor
  · intro h
    have hc := conjunctionRecover firstAccepted secondAccepted ![table,code] h
    exact andIntro ((childFactor firstField table code first hf).mp (andLeft hc))
      ((childFactor secondField table code second hs).mp (andRight hc))
  · intro h
    exact conjunctionAccept firstAccepted secondAccepted ![table,code]
      ((childFactor firstField table code first hf).mpr (andLeft h))
      ((childFactor secondField table code second hs).mpr (andRight h))

theorem ordinaryFactor (n : Nat) (table code first head : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 firstField first table code)))
    (hh : Nonempty (Derivation body Delta (graph2 headField head table code))) :
    Nonempty (Derivation body Delta (graph2 (ordinary n) (numeral 1) table code)) ↔
    Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head ⊓
      graph2 InternalRawListRecursion.lookup (numeral 1) first table)) := by
  constructor
  · intro h
    have hc := conjunctionRecover (headAccepted n) firstAccepted ![table,code] h
    exact andIntro ((headFactor n table code head hh).mp (andLeft hc))
      ((childFactor firstField table code first hf).mp (andRight hc))
  · intro h
    exact conjunctionAccept (headAccepted n) firstAccepted ![table,code]
      ((headFactor n table code head hh).mpr (andLeft h))
      ((childFactor firstField table code first hf).mpr (andRight h))

theorem numberedFactor (n : Nat) (table code first second head : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 firstField first table code)))
    (hs : Nonempty (Derivation body Delta (graph2 secondField second table code)))
    (hh : Nonempty (Derivation body Delta (graph2 headField head table code))) :
    Nonempty (Derivation body Delta (graph2 (numbered n) (numeral 1) table code)) ↔
    Nonempty (Derivation body Delta ((graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head ⊓
      graph2 InternalRawListRecursion.lookup (numeral 1) first table) ⊓
      graph2 InternalRawListRecursion.lookup (numeral 1) second table)) := by
  constructor
  · intro h
    have hc := conjunctionRecover (ordinary n) secondAccepted ![table,code] h
    exact andIntro ((ordinaryFactor n table code first head hf hh).mp (andLeft hc))
      ((childFactor secondField table code second hs).mp (andRight hc))
  · intro h
    exact conjunctionAccept (ordinary n) secondAccepted ![table,code]
      ((ordinaryFactor n table code first head hf hh).mpr (andLeft h))
      ((childFactor secondField table code second hs).mpr (andRight h))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.SupportProof
