module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.UnaryQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.UnarySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.MalformedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.UnaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel eqnRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalQuotientComparisonProof (orLeft orRight)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261115 OriginalCodeBoundsRecursion
open UnaryValueProof (constructor)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem resultRename {beta : Type} (n : Nat) (raw child out : OTerm alpha) (j : alpha → beta) :
    (unaryResult n raw child out).relabel j = unaryResult n (raw.relabel j) (child.relabel j) (out.relabel j) := by
  change (invalidResult n raw out ⊔ (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓ UnarySyntaxProof.block n child out)).relabel j = _
  simp only [invalidResult,InternalBetaBoundaryProof.supRename,conjunctionRename,graph1Rename,
    eqnRelabel,GuardedSourceSyntaxProof.numeralRename,UnarySyntaxProof.blockRename]
  rfl

theorem atGuard (ordinary : Bool) (n : Nat) (raw metadata child out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 (constructor ordinary) raw metadata child)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (ho : Nonempty (Derivation body Delta (graph1 (bounds n) out raw))) :
    Nonempty (Derivation body Delta (unaryResult n raw child out)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (UnaryQueriesProof.queries n) ![child] _
  intro beta j ys Theta hj hq
  rw [resultRename]
  have hx : (fun i => (![child] i).relabel j) = (![child.relabel j] : Fin 1 → OTerm beta) := by
    funext i
    obtain rfl := Fin.eq_zero i
    rfl
  rw [hx] at hq
  have hcj := renameInto hc j Theta hj
  have hgj := renameInto hg j Theta hj
  have hoj := renameInto ho j Theta hj
  simp only [graph1Rename,graph2Rename,sucRelabel,zRelabel] at hcj hgj hoj
  have hp := UnaryQueriesProof.childPair n (child.relabel j) (ys 0) (ys 1) (ys 2) (hq 0) (hq 1) (hq 2)
  have hnext := UnaryQueriesProof.nextPair n (child.relabel j) (ys 1) (ys 2) (ys 3) (hq 1) (hq 2) (hq 3)
  have hv := UnaryValueProof.value ordinary n (raw.relabel j) (metadata.relabel j) (child.relabel j)
    (ys 0) (ys 1) (ys 2) (ys 3) hcj hgj (hq 0) hp hnext
  obtain ⟨he⟩ := valueUnique (bounds n) (out.relabel j) (ys 3) ![raw.relabel j] hoj hv
  have hout := outputTransport InternalPairing.pairing (ys 3) (out.relabel j) ![suc (ys 1),ys 2] ⟨symm he⟩ hnext
  have hb := UnarySyntaxProof.introduce n (child.relabel j) (out.relabel j) ![ys 0,ys 1,ys 2]
    (andIntro (andIntro (hq 0) hp) hout)
  obtain ⟨h⟩ := andIntro hgj hb
  exact ⟨orRight h⟩

theorem forward (ordinary : Bool) (n : Nat) (raw metadata child out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 (constructor ordinary) raw metadata child)))
    (ho : Nonempty (Derivation body Delta (graph1 (bounds n) out raw))) :
    Nonempty (Derivation body Delta (unaryResult n raw child out)) := by
  apply CasesProof.guardCases n raw
  · intro beta j Theta hj hg
    rw [resultRename]
    have hoj := renameInto ho j Theta hj
    rw [graph1Rename] at hoj
    have he := valueUnique (bounds n) (out.relabel j) z ![raw.relabel j] hoj
      (MalformedProof.malformedValue n (raw.relabel j) hg)
    obtain ⟨h⟩ := andIntro hg he
    exact ⟨orLeft h⟩
  · intro beta j Theta hj hg
    rw [resultRename]
    have hcj := renameInto hc j Theta hj
    have hoj := renameInto ho j Theta hj
    rw [graph2Rename] at hcj
    rw [graph1Rename] at hoj
    exact atGuard ordinary n (raw.relabel j) (metadata.relabel j) (child.relabel j) (out.relabel j) hcj hg hoj

theorem backward (ordinary : Bool) (n : Nat) (raw metadata child out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 (constructor ordinary) raw metadata child)))
    (hw : Nonempty (Derivation body Delta (unaryResult n raw child out))) :
    Nonempty (Derivation body Delta (graph1 (bounds n) out raw)) := by
  apply OriginalTypedDecoderInternalBranchProof.orCases hw
  · let L := invalidResult n raw out
    have hl : Nonempty (Derivation body (L :: Delta) L) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := andRight hl
    exact outputTransport (bounds n) z out ![raw] ⟨symm he⟩
      (MalformedProof.malformedValue n raw (andLeft hl))
  · let R := graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓ UnarySyntaxProof.block n child out
    have hr : Nonempty (Derivation body (R :: Delta) R) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply UnarySyntaxProof.cases n child out _ (andRight hr)
    intro beta j Theta ys hj hf
    rw [graph1Rename]
    have hcj := renameInto (withHyp hc R) j Theta hj
    have hgj := renameInto (andLeft hr) j Theta hj
    rw [graph2Rename] at hcj
    simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hgj
    exact UnaryValueProof.value ordinary n (raw.relabel j) (metadata.relabel j) (child.relabel j)
      (ys 0) (ys 1) (ys 2) (out.relabel j) hcj hgj (andLeft (andLeft hf)) (andRight (andLeft hf)) (andRight hf)

theorem internalLambda : Targets.InternalLambda := by
  intro n body alpha Delta raw out typ child hc
  exact ⟨forward false n raw typ child out hc,backward false n raw typ child out hc⟩
theorem internalOrdinary : Targets.InternalOrdinary := by
  intro n body alpha Delta raw out head child hc
  exact ⟨forward true n raw head child out hc,backward true n raw head child out hc⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.UnaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.UnaryProof
