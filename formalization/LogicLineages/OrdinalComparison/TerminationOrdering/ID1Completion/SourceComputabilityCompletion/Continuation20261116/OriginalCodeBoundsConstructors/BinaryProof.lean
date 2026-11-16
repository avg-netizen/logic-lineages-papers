module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinarySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.MalformedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryProof
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
open BinaryRootProof (constructor)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem resultRename {beta : Type} (n : Nat) (cons : Bool) (raw left right out : OTerm alpha) (j : alpha → beta) :
    (binaryResult n cons raw left right out).relabel j = binaryResult n cons (raw.relabel j) (left.relabel j) (right.relabel j) (out.relabel j) := by
  change (invalidResult n raw out ⊔ (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓ BinarySyntaxProof.block n cons left right out)).relabel j = _
  simp only [invalidResult,InternalBetaBoundaryProof.supRename,conjunctionRename,graph1Rename,
    eqnRelabel,GuardedSourceSyntaxProof.numeralRename,BinarySyntaxProof.blockRename]
  rfl

theorem atGuard (cons : Bool) (n : Nat) (raw typ left right out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 (constructor cons) raw typ left right)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (ho : Nonempty (Derivation body Delta (graph1 (bounds n) out raw))) :
    Nonempty (Derivation body Delta (binaryResult n cons raw left right out)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (BinaryQueriesProof.queries n cons) ![left,right] _
  intro beta j ys Theta hj hq
  rw [resultRename]
  have hx : (fun i => (![left,right] i).relabel j) = (![left.relabel j,right.relabel j] : Fin 2 → OTerm beta) := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hq
  have hcj := renameInto hc j Theta hj
  have hgj := renameInto hg j Theta hj
  have hoj := renameInto ho j Theta hj
  simp only [graph1Rename,graph3Rename,sucRelabel,zRelabel] at hcj hgj hoj
  obtain ⟨hel,hl,her,hr,hm,hnext⟩ := BinaryQueriesProof.recover n cons (left.relabel j) (right.relabel j) ys hq
  have hv := BinaryValueProof.value cons n (raw.relabel j) (typ.relabel j) (left.relabel j) (right.relabel j)
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) hcj hgj hel her hl hr hm hnext
  obtain ⟨he⟩ := valueUnique (bounds n) (out.relabel j) (ys 7) ![raw.relabel j] hoj hv
  have hout := outputTransport InternalPairing.pairing (ys 7) (out.relabel j)
    ![if cons then OrdinaryArithmetic.addTerm (ys 1) (ys 4) else suc (OrdinaryArithmetic.addTerm (ys 1) (ys 4)),ys 6]
    ⟨symm he⟩ hnext
  have hb := BinarySyntaxProof.introduce n cons (left.relabel j) (right.relabel j) (out.relabel j)
    ![ys 0,ys 1,ys 2,ys 3,ys 4,ys 5,ys 6]
    (andIntro (andIntro (andIntro (andIntro (andIntro hel hl) her) hr) hm) hout)
  obtain ⟨h⟩ := andIntro hgj hb
  exact ⟨orRight h⟩

theorem forward (cons : Bool) (n : Nat) (raw typ left right out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 (constructor cons) raw typ left right)))
    (ho : Nonempty (Derivation body Delta (graph1 (bounds n) out raw))) :
    Nonempty (Derivation body Delta (binaryResult n cons raw left right out)) := by
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
    rw [graph3Rename] at hcj
    rw [graph1Rename] at hoj
    exact atGuard cons n (raw.relabel j) (typ.relabel j) (left.relabel j) (right.relabel j) (out.relabel j) hcj hg hoj

theorem backward (cons : Bool) (n : Nat) (raw typ left right out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 (constructor cons) raw typ left right)))
    (hw : Nonempty (Derivation body Delta (binaryResult n cons raw left right out))) :
    Nonempty (Derivation body Delta (graph1 (bounds n) out raw)) := by
  apply OriginalTypedDecoderInternalBranchProof.orCases hw
  · let L := invalidResult n raw out
    have hl : Nonempty (Derivation body (L :: Delta) L) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := andRight hl
    exact outputTransport (bounds n) z out ![raw] ⟨symm he⟩
      (MalformedProof.malformedValue n raw (andLeft hl))
  · let R := graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓ BinarySyntaxProof.block n cons left right out
    have hr : Nonempty (Derivation body (R :: Delta) R) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply BinarySyntaxProof.cases n cons left right out _ (andRight hr)
    intro beta j Theta ys hj hf
    rw [graph1Rename]
    have hcj := renameInto (withHyp hc R) j Theta hj
    have hgj := renameInto (andLeft hr) j Theta hj
    rw [graph3Rename] at hcj
    simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hgj
    exact BinaryValueProof.value cons n (raw.relabel j) (typ.relabel j) (left.relabel j) (right.relabel j)
      (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (out.relabel j) hcj hgj
      (andLeft (andLeft (andLeft (andLeft (andLeft hf)))))
      (andRight (andLeft (andLeft (andLeft hf))))
      (andRight (andLeft (andLeft (andLeft (andLeft hf)))))
      (andRight (andLeft (andLeft hf))) (andRight (andLeft hf)) (andRight hf)

theorem internalApplication : Targets.InternalApplication := by
  intro n body alpha Delta raw out typ left right hc
  exact ⟨forward false n raw typ left right out hc,backward false n raw typ left right out hc⟩
theorem internalCons : Targets.InternalCons := by
  intro n body alpha Delta raw out typ left right hc
  exact ⟨forward true n raw typ left right out hc,backward true n raw typ left right out hc⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryProof
