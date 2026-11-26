module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteSignatureEquations.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteSignatureEquations.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalConcreteHeadSignature
open Continuation20261115.OriginalHeadDecoderValidity.SupportProof
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem outputEquation (n : Nat) (arity : Fin n → Nat) (raw packed out : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 (signature n arity) (suc packed) raw))) :
    Nonempty (Derivation body Delta (graph1 (signature n arity) out raw)) ↔
    Nonempty (Derivation body Delta (eqn out (suc packed))) := by
  constructor
  · intro h
    exact valueUnique (signature n arity) out (suc packed) ![raw] h hv
  · rintro ⟨he⟩
    exact outputTransport (signature n arity) (suc packed) out ![raw] ⟨symm he⟩ hv

theorem applicationSignature : Targets.InternalApplicationSignature := by
  intro n arity body alpha Delta raw payload domain result tail args packed out hp hd ht ha hk
  obtain ⟨hi⟩ := InternalRecursionClosureLogicProof.closedApply
    (InternalUnpairProof.actualOriginalGeneratedCodeInverse body alpha payload domain result) hd
  have hr : Nonempty (Derivation body Delta (graph1 OriginalHeadResult.headResult result raw)) :=
    (OriginalHeadResult.InternalProof.internalTagFactor body alpha Delta (4 : Fin 6)
      raw payload result hp).mpr ⟨Derivation.conjunctionRight hi⟩
  have hargs := (OriginalConcreteHeadArguments.BranchProof.applicationArguments n arity body alpha Delta
    raw payload domain result tail args hp hd ht).mpr ha
  have hg : Nonempty (Derivation body Delta
      (graph1 (Continuation20261115.OriginalHeadDecoderValidity.check n) (suc z) raw)) :=
    (tagFactor n (4 : Fin 6) raw (numeral 4) payload (numeral 1) hp ⟨refl (numeral 4)⟩).mpr
      (constantValue 1 ![raw])
  exact outputEquation n arity raw packed out
    (OriginalConcreteHeadSignature.OutputProof.successValue n arity raw result args packed hr hargs hk hg)

theorem rankedSignature : Targets.InternalRankedSignature := by
  intro n arity body alpha Delta raw symbol count args packed out hp hb hl ha hk
  obtain ⟨hi⟩ := InternalRecursionClosureLogicProof.closedApply
    (InternalUnpairProof.actualOriginalGeneratedCodeInverse body alpha raw (numeral 5) symbol) hp
  have hright : Nonempty (Derivation body Delta (graph1 InternalUnpair.right symbol raw)) :=
    ⟨Derivation.conjunctionRight hi⟩
  have hr : Nonempty (Derivation body Delta (graph1 OriginalHeadResult.headResult z raw)) :=
    (OriginalHeadResult.InternalProof.internalTagFactor body alpha Delta (5 : Fin 6)
      raw symbol z hp).mpr (constantValue 0 ![symbol])
  have hargs := (OriginalConcreteHeadArguments.BranchProof.rankedArguments n arity body alpha Delta
    raw symbol count args hp hl).mpr ha
  have hg : Nonempty (Derivation body Delta
      (graph1 (Continuation20261115.OriginalHeadDecoderValidity.check n) (suc z) raw)) :=
    (tagFactor n (5 : Fin 6) raw (numeral 5) symbol (numeral 1) hp ⟨refl (numeral 5)⟩).mpr
      ((rankedFactor n raw symbol hright).mpr hb)
  exact outputEquation n arity raw packed out
    (OriginalConcreteHeadSignature.OutputProof.successValue n arity raw z args packed hr hargs hk hg)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteSignatureEquations.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteSignatureEquations.Proof
