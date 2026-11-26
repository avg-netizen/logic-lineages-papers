module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AnnotationSuffixSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AnnotationSuffixDecorationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalInternalIndexedPrefixCasesTargets (bump)
open OriginalInternalJobDeletionLookupProof (bumpRename)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open InheritedMapDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph InternalPairing.pairing InternalUnpair.left
  InternalUnpair.right OriginalHereditaryAnnotatedExpansion.annotation

theorem atPairs (arity : Nat) (offset typ raw rawHead mark typed annotated : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral arity) raw)))
    (hm : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mark z typ)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawHead)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing annotated z typed))) :
    Nonempty (Derivation body Delta
      (graph5 OriginalHereditaryAnnotatedExpansion.decorate annotated (bump arity offset) z typ raw rawHead)) := by
  have hn := OriginalInternalAnnotationOffsetProof.notBelowBump (body := body) (Delta := Delta) arity offset
  have hv := OriginalInternalAnnotationInheritedProof.actualInherited body alpha Delta
    (bump arity offset) z typ raw (numeral arity) mark ha hn hm
  let xs : Fin 5 → OTerm alpha := ![bump arity offset,z,typ,raw,rawHead]
  let a : Program 5 := .composition OriginalHereditaryAnnotatedExpansion.annotation
    ![.projection 0,.projection 1,.projection 2,.projection 3]
  have av : Nonempty (Derivation body Delta (programGraph a mark xs)) := by
    apply compositionValue OriginalHereditaryAnnotatedExpansion.annotation
      ![.projection 0,.projection 1,.projection 2,.projection 3] mark xs
      ![bump arity offset,z,typ,raw] hv
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)))) i
    · exact projectionValue 0 xs
    · exact projectionValue 1 xs
    · exact projectionValue 2 xs
    · exact projectionValue 3 xs
  have hl := unaryValue InternalUnpair.left a z mark xs (pairLeft mark z typ hm) av
  have hr := unaryValue InternalUnpair.right a typ mark xs (pairRight mark z typ hm) av
  have htyped := binaryValue InternalPairing.pairing (rightOf a) (.projection 4)
    typed typ rawHead xs ht hr (projectionValue 4 xs)
  exact binaryValue InternalPairing.pairing (leftOf a) (pairOf (rightOf a) (.projection 4))
    annotated z typed xs hp hl htyped

theorem actualDecoration (arity : Nat) (offset typ raw rawHead annotated : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral arity) raw)))
    (hh : Nonempty (Derivation body Delta (graph2 inheritedJob annotated rawHead typ))) :
    Nonempty (Derivation body Delta
      (graph5 OriginalHereditaryAnnotatedExpansion.decorate annotated (bump arity offset) z typ raw rawHead)) := by
  let mark : Program 2 := pairOf (OriginalRawSyntaxTransport.constant 2 0) (.projection 1)
  let typed : Program 2 := pairOf (.projection 1) (.projection 0)
  let qs : Fin 2 → Program 2 := ![mark,typed]
  let xs : Fin 2 → OTerm alpha := ![rawHead,typ]
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  simp only [graph5Rename,bumpRename,zRelabel]
  let xx : Fin 2 → OTerm beta := ![rawHead.relabel j,typ.relabel j]
  have hx : (fun i => (xs i).relabel j) = xx := by
    funext i
    refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i
    · rfl
    · rfl
  rw [hx] at hq
  have qm : Nonempty (Derivation body Theta (programGraph mark (ys 0) xx)) := hq 0
  have qt : Nonempty (Derivation body Theta (programGraph typed (ys 1) xx)) := hq 1
  have hm := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 0) (.projection 1)
    (ys 0) z (typ.relabel j) xx qm (constantValue 0 xx) (projectionValue 1 xx)
  have ht := binaryRecover InternalPairing.pairing (.projection 1) (.projection 0)
    (ys 1) (typ.relabel j) (rawHead.relabel j) xx qt (projectionValue 1 xx) (projectionValue 0 xx)
  have ha' := renameInto ha j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at ha'
  have hh' := renameInto hh j Theta hj
  rw [graph2Rename] at hh'
  have hp := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 0) typed
    (annotated.relabel j) z (ys 1) xx hh' (constantValue 0 xx) qt
  exact atPairs arity (offset.relabel j) (typ.relabel j) (raw.relabel j) (rawHead.relabel j)
    (ys 0) (ys 1) (annotated.relabel j) ha' hm ht hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AnnotationSuffixDecorationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AnnotationSuffixDecorationProof
