module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.BinaryValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.BinaryQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.LeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.NumberedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel eqnRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalQuotientComparisonProof (orLeft orRight)
open SourceComputabilityFormulaSupportProof (numeral)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem resultRename {beta : Type} (n : Nat) (raw left right out : OTerm alpha) (j : alpha → beta) :
    (Targets.binaryResult n raw left right out).relabel j = Targets.binaryResult n (raw.relabel j) (left.relabel j) (right.relabel j) (out.relabel j) := by
  change (Targets.invalidResult n raw out ⊔ (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓ BinarySyntaxProof.block n left right out)).relabel j = _
  simp only [Targets.invalidResult,LeafProof.orRename,conjunctionRename,graph1Rename,
    eqnRelabel,GuardedSourceSyntaxProof.numeralRename,BinarySyntaxProof.blockRename]
  rfl

theorem forward (n : Nat) (raw label head typ left types right out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw ![label,head,typ,left,types,right])))
    (ho : Nonempty (Derivation body Delta (graph1 (depth n) out raw))) :
    Nonempty (Derivation body Delta (Targets.binaryResult n raw left right out)) := by
  apply OriginalCodeBoundsRecursion.CasesProof.guardCases n raw
  · intro beta j Theta hj hg
    rw [resultRename]
    have hoj := renameInto ho j Theta hj
    rw [graph1Rename] at hoj
    have he := valueUnique (depth n) (out.relabel j) z ![raw.relabel j] hoj (ValueProof.malformedValue n (raw.relabel j) hg)
    obtain ⟨h⟩ := andIntro hg he
    exact ⟨orLeft h⟩
  · intro beta j Theta hj hg
    rw [resultRename]
    have hcj := renameInto hc j Theta hj
    rw [BinaryValueProof.numberedRename] at hcj
    have hoj := renameInto ho j Theta hj
    rw [graph1Rename] at hoj
    apply BinaryQueriesProof.cases n (left.relabel j) (right.relabel j)
    intro gamma k Xi dl dr maximum hk hl hr hm
    rw [resultRename]
    have hck := renameInto hcj k Xi hk
    rw [BinaryValueProof.numberedRename] at hck
    have hgk := renameInto hg k Xi hk
    simp only [graph1Rename,sucRelabel,zRelabel] at hgk
    have hok := renameInto hoj k Xi hk
    rw [graph1Rename] at hok
    have he := valueUnique (depth n) ((out.relabel j).relabel k) (suc maximum) ![(raw.relabel j).relabel k] hok
      (BinaryValueProof.numbered n ((raw.relabel j).relabel k) ((label.relabel j).relabel k) ((head.relabel j).relabel k) ((typ.relabel j).relabel k)
        ((left.relabel j).relabel k) ((types.relabel j).relabel k) ((right.relabel j).relabel k) dl dr maximum hck hgk hl hr hm)
    have hb := BinarySyntaxProof.introduce n ((left.relabel j).relabel k) ((right.relabel j).relabel k)
      ((out.relabel j).relabel k) ![dl,dr,maximum] (andIntro (andIntro (andIntro hl hr) hm) he)
    obtain ⟨h⟩ := andIntro hgk hb
    exact ⟨orRight h⟩

theorem backward (n : Nat) (raw label head typ left types right out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw ![label,head,typ,left,types,right])))
    (hw : Nonempty (Derivation body Delta (Targets.binaryResult n raw left right out))) :
    Nonempty (Derivation body Delta (graph1 (depth n) out raw)) := by
  let L := Targets.invalidResult n raw out
  let R := graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓ BinarySyntaxProof.block n left right out
  have hl : Nonempty (Derivation body (L :: Delta) L) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hr : Nonempty (Derivation body (R :: Delta) R) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨el⟩ := andRight hl
  obtain ⟨vl⟩ := outputTransport (depth n) z out ![raw] ⟨symm el⟩ (ValueProof.malformedValue n raw (andLeft hl))
  have vr : Nonempty (Derivation body (R :: Delta) (graph1 (depth n) out raw)) := by
    apply BinarySyntaxProof.cases n left right out _ (andRight hr)
    intro beta j Theta ys hj hf
    rw [graph1Rename]
    have hcj := renameInto (withHyp hc R) j Theta hj
    rw [BinaryValueProof.numberedRename] at hcj
    have hgj := renameInto (andLeft hr) j Theta hj
    simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hgj
    obtain ⟨he⟩ := andRight hf
    exact outputTransport (depth n) (suc (ys 2)) (out.relabel j) ![raw.relabel j] ⟨symm he⟩
      (BinaryValueProof.numbered n (raw.relabel j) (label.relabel j) (head.relabel j) (typ.relabel j) (left.relabel j) (types.relabel j) (right.relabel j)
        (ys 0) (ys 1) (ys 2) hcj hgj (andLeft (andLeft (andLeft hf))) (andRight (andLeft (andLeft hf))) (andRight (andLeft hf)))
  obtain ⟨vr⟩ := vr
  obtain ⟨hw⟩ := hw
  exact ⟨InternalBetaTotalityProof.disjunctionElimination hw
    (Derivation.implicationIntroduction vl) (Derivation.implicationIntroduction vr)⟩

theorem internalNumbered : Targets.InternalNumbered := by
  intro n body alpha Delta raw out label head typ base types extra hc
  exact ⟨forward n raw label head typ base types extra out hc,backward n raw label head typ base types extra out hc⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.NumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.NumberedProof
