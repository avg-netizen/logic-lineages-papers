module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NilValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.MalformedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NilProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel eqnRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename emptyRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalQuotientComparisonProof (orLeft orRight)
open Continuation20261115 OriginalCodeBoundsRecursion
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem leafRename {beta : Type} (n : Nat) (raw out : OTerm alpha) (j : alpha → beta) :
    (leafResult n raw out 0).relabel j = leafResult n (raw.relabel j) (out.relabel j) 0 := by
  simp only [leafResult,invalidResult,InternalBetaBoundaryProof.supRename,conjunctionRename,
    graph1Rename,graph2Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename]

theorem forward (n : Nat) (raw out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0)))
    (ho : Nonempty (Derivation body Delta (graph1 (bounds n) out raw))) :
    Nonempty (Derivation body Delta (leafResult n raw out 0)) := by
  apply CasesProof.guardCases n raw
  · intro beta j Theta hj hg
    rw [leafRename]
    have hoj := renameInto ho j Theta hj
    rw [graph1Rename] at hoj
    have he := valueUnique (bounds n) (out.relabel j) z ![raw.relabel j] hoj
      (MalformedProof.malformedValue n (raw.relabel j) hg)
    obtain ⟨h⟩ := andIntro hg he
    exact ⟨orLeft h⟩
  · intro beta j Theta hj hg
    rw [leafRename]
    have hoj := renameInto ho j Theta hj
    have hcj := renameInto hc j Theta hj
    rw [graph1Rename] at hoj
    simp only [programRename,emptyRename] at hcj
    have hp := InternalApplicationValidityStackAppendTransitionProof.pairZero (body := body) (Gamma := Theta) (α := beta)
    have hv := NilValueProof.nilValue n (raw.relabel j) hcj hg
    obtain ⟨he⟩ := valueUnique (bounds n) (out.relabel j) z ![raw.relabel j] hoj hv
    have hout := outputTransport InternalPairing.pairing z (out.relabel j)
      ![z,z] ⟨symm he⟩ hp
    obtain ⟨h⟩ := andIntro hg hout
    exact ⟨orRight h⟩

theorem backward (n : Nat) (raw out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0)))
    (hw : Nonempty (Derivation body Delta (leafResult n raw out 0))) :
    Nonempty (Derivation body Delta (graph1 (bounds n) out raw)) := by
  apply OriginalTypedDecoderInternalBranchProof.orCases hw
  · let L := invalidResult n raw out
    have hl : Nonempty (Derivation body (L :: Delta) L) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := andRight hl
    exact outputTransport (bounds n) z out ![raw] ⟨symm he⟩
      (MalformedProof.malformedValue n raw (andLeft hl))
  · let R := graph1 (OriginalCodeValidityGuard.check n) (suc z) raw ⊓
      graph2 InternalPairing.pairing out z z
    have hr : Nonempty (Derivation body (R :: Delta) R) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hz := NilValueProof.nilValue n raw (withHyp hc R) (andLeft hr)
    obtain ⟨he⟩ := valueUnique InternalPairing.pairing out z ![z,z] (andRight hr)
      InternalApplicationValidityStackAppendTransitionProof.pairZero
    exact outputTransport (bounds n) z out ![raw] ⟨symm he⟩ hz

theorem internalNil : Targets.InternalNil := by
  intro n body alpha Delta raw out hc
  exact ⟨forward n raw out hc,backward n raw out hc⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NilProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NilProof
