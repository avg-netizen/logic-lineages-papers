module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NumberedQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NumberedSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.MalformedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NumberedProof
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
open OriginalRawSyntaxTransport
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem resultRename {beta : Type} (n : Nat) (raw rootLabel left right out : OTerm alpha) (j : alpha → beta) :
    (numberedResult n raw rootLabel left right out).relabel j = numberedResult n (raw.relabel j) (rootLabel.relabel j) (left.relabel j) (right.relabel j) (out.relabel j) := by
  change (invalidResult n raw out ⊔ (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓ NumberedSyntaxProof.block n rootLabel left right out)).relabel j = _
  simp only [invalidResult,InternalBetaBoundaryProof.supRename,conjunctionRename,graph1Rename,
    eqnRelabel,GuardedSourceSyntaxProof.numeralRename,NumberedSyntaxProof.blockRename]
  rfl

theorem atGuard (n : Nat) (raw rootLabel head typ left types right out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![rootLabel,head,typ,left,types,right])))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (ho : Nonempty (Derivation body Delta (graph1 (bounds n) out raw))) :
    Nonempty (Derivation body Delta (numberedResult n raw rootLabel left right out)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (NumberedQueriesProof.queries n) ![rootLabel,left,right] _
  intro beta j ys Theta hj hq
  rw [resultRename]
  have hx : (fun i => (![rootLabel,left,right] i).relabel j) = (![rootLabel.relabel j,left.relabel j,right.relabel j] : Fin 3 → OTerm beta) := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hq
  have hcj := renameInto hc j Theta hj
  have hgj := renameInto hg j Theta hj
  have hoj := renameInto ho j Theta hj
  rw [OriginalEnumerationDepth.BinaryValueProof.numberedRename] at hcj
  simp only [graph1Rename,sucRelabel,zRelabel] at hgj hoj
  obtain ⟨hel,hl,her,hr,hm,hmax,hnext⟩ := NumberedQueriesProof.recover n (rootLabel.relabel j) (left.relabel j) (right.relabel j) ys hq
  have hv := NumberedValueProof.value n (raw.relabel j) (rootLabel.relabel j) (head.relabel j) (typ.relabel j)
    (left.relabel j) (types.relabel j) (right.relabel j)
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 8) (ys 9) hcj hgj hel her hl hr hm hmax hnext
  obtain ⟨he⟩ := valueUnique (bounds n) (out.relabel j) (ys 9) ![raw.relabel j] hoj hv
  have hout := outputTransport InternalPairing.pairing (ys 9) (out.relabel j)
    ![suc (OrdinaryArithmetic.addTerm (ys 1) (ys 4)),ys 8] ⟨symm he⟩ hnext
  have hb := NumberedSyntaxProof.introduce n (rootLabel.relabel j) (left.relabel j) (right.relabel j) (out.relabel j)
    ![ys 0,ys 1,ys 2,ys 3,ys 4,ys 5,ys 6,ys 8]
    (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro hel hl) her) hr) hm) hmax) hout)
  obtain ⟨h⟩ := andIntro hgj hb
  exact ⟨orRight h⟩

theorem forward (n : Nat) (raw rootLabel head typ left types right out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![rootLabel,head,typ,left,types,right])))
    (ho : Nonempty (Derivation body Delta (graph1 (bounds n) out raw))) :
    Nonempty (Derivation body Delta (numberedResult n raw rootLabel left right out)) := by
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
    rw [OriginalEnumerationDepth.BinaryValueProof.numberedRename] at hcj
    rw [graph1Rename] at hoj
    exact atGuard n (raw.relabel j) (rootLabel.relabel j) (head.relabel j) (typ.relabel j) (left.relabel j) (types.relabel j) (right.relabel j) (out.relabel j) hcj hg hoj

theorem backward (n : Nat) (raw rootLabel head typ left types right out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![rootLabel,head,typ,left,types,right])))
    (hw : Nonempty (Derivation body Delta (numberedResult n raw rootLabel left right out))) :
    Nonempty (Derivation body Delta (graph1 (bounds n) out raw)) := by
  apply OriginalTypedDecoderInternalBranchProof.orCases hw
  · let L := invalidResult n raw out
    have hl : Nonempty (Derivation body (L :: Delta) L) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := andRight hl
    exact outputTransport (bounds n) z out ![raw] ⟨symm he⟩
      (MalformedProof.malformedValue n raw (andLeft hl))
  · let R := graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓ NumberedSyntaxProof.block n rootLabel left right out
    have hr : Nonempty (Derivation body (R :: Delta) R) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply NumberedSyntaxProof.cases n rootLabel left right out _ (andRight hr)
    intro beta j Theta ys hj hf
    rw [graph1Rename]
    have hcj := renameInto (withHyp hc R) j Theta hj
    have hgj := renameInto (andLeft hr) j Theta hj
    rw [OriginalEnumerationDepth.BinaryValueProof.numberedRename] at hcj
    simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hgj
    exact NumberedValueProof.value n (raw.relabel j) (rootLabel.relabel j) (head.relabel j) (typ.relabel j)
      (left.relabel j) (types.relabel j) (right.relabel j)
      (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (out.relabel j) hcj hgj
      (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft hf))))))
      (andRight (andLeft (andLeft (andLeft (andLeft hf)))))
      (andRight (andLeft (andLeft (andLeft (andLeft (andLeft hf))))))
      (andRight (andLeft (andLeft (andLeft hf))))
      (andRight (andLeft (andLeft hf))) (andRight (andLeft hf)) (andRight hf)

theorem internalNumbered : Targets.InternalNumbered := by
  intro n body alpha Delta raw out label head typ base types extra hc
  exact ⟨forward n raw label head typ base types extra out hc,backward n raw label head typ base types extra out hc⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NumberedProof
