module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalOriginalUniformVertexPathSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem windowGraph (n : Nat) (arity : Fin n → Nat) (value head rest symbols types : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) value head symbols types))) :
    Nonempty (Derivation body Delta (programGraph
      (.composition (OriginalHeadWindow.window n arity) ![.projection 0,.projection 2,.projection 3]) value
      ![head,rest,symbols,types])) :=
  ternaryValue (OriginalHeadWindow.window n arity) (.projection 0) (.projection 2) (.projection 3)
    value head symbols types ![head,rest,symbols,types] h (projectionValue 0 ![head,rest,symbols,types])
    (projectionValue 2 ![head,rest,symbols,types]) (projectionValue 3 ![head,rest,symbols,types])

theorem internalFilterNil : Targets.InternalFilterNil := by
  intro n arity body alpha Delta symbols types
  exact InternalRawListRecursionProof.nilValue (constant 2 0) (filterStep n arity) (numeral 0)
    (Fin.cons symbols (Fin.cons types Fin.elim0))
    (constantValue 0 (Fin.cons symbols (Fin.cons types Fin.elim0)))

theorem internalFilterCons : Targets.InternalFilterCons := by
  intro n arity body alpha Delta list head tail rest symbols types hc hr
  let xs : Fin 4 → OTerm alpha := ![head,rest,symbols,types]
  let control : Program 4 := .composition (OriginalHeadWindow.window n arity) ![.projection 0,.projection 2,.projection 3]
  constructor
  · intro hw
    have hs := zeroBranchIntro control (.projection 1) (consOf (.projection 0) (.projection 1)) rest xs
      (windowGraph n arity (numeral 0) head rest symbols types hw) (projectionValue 1 xs)
    exact InternalRawListRecursionProof.consValue (constant 2 0) (filterStep n arity) list head tail rest rest
      (Fin.cons symbols (Fin.cons types Fin.elim0)) hc hr hs
  · intro out hw ho
    have hcons := binaryValue InternalListCodec.consCode (.projection 0) (.projection 1) out head rest xs ho
      (projectionValue 0 xs) (projectionValue 1 xs)
    have hs := successorBranchIntro control (.projection 1) (consOf (.projection 0) (.projection 1)) out (numeral 0) xs
      (windowGraph n arity (numeral 1) head rest symbols types hw) hcons
    exact InternalRawListRecursionProof.consValue (constant 2 0) (filterStep n arity) list head tail rest out
      (Fin.cons symbols (Fin.cons types Fin.elim0)) hc hr hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.InternalProof
