module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem ownTable (n : Nat) (raw table : OTerm alpha)
    (ht : Nonempty (Derivation body Delta
      (graph2 (OriginalCodeDecoderTable.tableProgram n) table (suc raw) raw))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.table n) table raw)) := by
  exact binaryValue (OriginalCodeDecoderTable.tableProgram n) (succOf (.projection 0)) (.projection 0)
    table (suc raw) raw (Fin.cons raw Fin.elim0) ht
    (OriginalCodeDecoderTable.SupportProof.succProjection 0 (Fin.cons raw Fin.elim0))
    (projectionValue 0 (Fin.cons raw Fin.elim0))

theorem checkIntro (n : Nat) (raw table value : OTerm alpha)
    (ht : Nonempty (Derivation body Delta
      (graph2 (OriginalCodeDecoderTable.tableProgram n) table (suc raw) raw)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value raw table))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) value raw)) := by
  exact binaryValue InternalRawListRecursion.lookup (.projection 0) (OriginalCodeValidityGuard.table n)
    value raw table (Fin.cons raw Fin.elim0) hl
    (projectionValue 0 (Fin.cons raw Fin.elim0)) (ownTable n raw table ht)

theorem checkRecover (n : Nat) (raw table value : OTerm alpha)
    (ht : Nonempty (Derivation body Delta
      (graph2 (OriginalCodeDecoderTable.tableProgram n) table (suc raw) raw)))
    (hc : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) value raw))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value raw table)) := by
  exact binaryRecover InternalRawListRecursion.lookup (.projection 0) (OriginalCodeValidityGuard.table n)
    value raw table (Fin.cons raw Fin.elim0) hc
    (projectionValue 0 (Fin.cons raw Fin.elim0)) (ownTable n raw table ht)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.SupportProof
