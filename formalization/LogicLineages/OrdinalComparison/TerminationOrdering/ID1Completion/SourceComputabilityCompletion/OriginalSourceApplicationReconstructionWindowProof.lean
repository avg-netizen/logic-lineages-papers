module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionWindowProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Recover the actual context-window graph from the original exposed
parameter pair. No closed-input evaluation or native calibration is used. -/
theorem windowAtContext (window : Program 1) (context : Nat)
    (function parameter gammaCode : OTerm alpha)
    (hw : Nonempty (Derivation body Gamma
      (OriginalFunctionNeutrality.windowGraph window function parameter)))
    (hp : Nonempty (Derivation body Gamma
      (graph2 InternalPairing.pairing parameter (numeral context) gammaCode))) :
    Nonempty (Derivation body Gamma
      (graph1 window InternalOriginalStepGuard.one (numeral context))) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons function (Fin.cons parameter Fin.elim0)
  have hl := pairLeft parameter (numeral context) gammaCode hp
  have hleft := unaryValue InternalUnpair.left (.projection (1 : Fin 2))
    (numeral context) parameter xs hl (projectionValue 1 xs)
  exact unaryRecover window (leftOf (.projection (1 : Fin 2)))
    InternalOriginalStepGuard.one (numeral context) xs hw hleft

/-- Build every literal raw-vertex activation conjunct from the original
window/parameter/arrow graphs and the two selected typed graphs. -/
theorem rawActivation (data : Data) (window : Program 1) (context : Nat)
    (arrow d e function argument parameter gammaCode : OTerm alpha)
    (hw : Nonempty (Derivation body Gamma
      (graph1 window InternalOriginalStepGuard.one (numeral context))))
    (hp : Nonempty (Derivation body Gamma
      (graph2 InternalPairing.pairing parameter (numeral context) gammaCode)))
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hf : Nonempty (Derivation body Gamma
      (InternalOriginalUniformApplicationTyping.typedGraph data function arrow parameter)))
    (ha : Nonempty (Derivation body Gamma
      (InternalOriginalUniformApplicationTyping.typedGraph data argument d parameter))) :
    Nonempty (Derivation body Gamma
      (programGraph (Path.activation data window) InternalOriginalStepGuard.one
        (Path.arguments parameter d e argument function))) := by
  let xs := Path.arguments parameter d e argument function
  have hl := pairLeft parameter (numeral context) gammaCode hp
  have hwindow := unaryValue window (leftOf (.projection (0 : Fin 5)))
    InternalOriginalStepGuard.one (numeral context) xs hw
    (unaryValue InternalUnpair.left (.projection (0 : Fin 5)) (numeral context) parameter xs
      hl (projectionValue 0 xs))
  have harrow := binaryValue InternalListCodec.consCode (.projection 1) (.projection 2)
    arrow d e xs har (projectionValue 1 xs) (projectionValue 2 xs)
  have hfunction := PathSupportProof.typedValue data (.projection 4)
    (consOf (.projection 1) (.projection 2)) (.projection 0)
    function arrow parameter xs (projectionValue 4 xs) harrow (projectionValue 0 xs) hf
  have hargument := PathSupportProof.typedValue data (.projection 3) (.projection 1) (.projection 0)
    argument d parameter xs (projectionValue 3 xs) (projectionValue 1 xs) (projectionValue 0 xs) ha
  exact conjunctionAccept _ _ xs hwindow (conjunctionAccept _ _ xs hfunction hargument)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionWindowProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionWindowProof
