module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ChildValuesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ListsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.UnarySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.LeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.UnaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel eqnRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalQuotientComparisonProof (orLeft orRight)
open SourceComputabilityFormulaSupportProof (numeral)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def constructor (ordinary : Bool) := if ordinary then OriginalRawSyntaxTransport.ordinaryConstructor else OriginalRawSyntaxTransport.lambdaConstructor

theorem value (ordinary : Bool) (n : Nat) (raw metadata child d : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 (constructor ordinary) raw metadata child)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (he : Nonempty (Derivation body Delta (graph1 (depth n) d child))) :
    Nonempty (Derivation body Delta (graph1 (depth n) (suc d) raw)) := by
  apply ListsProof.unary child d
  intro beta j Theta deps values hj hd hv
  simp only [graph1Rename,sucRelabel]
  have hcj := renameInto hc j Theta hj
  rw [graph2Rename] at hcj
  have hgj := renameInto hg j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hgj
  have hej := renameInto he j Theta hj
  rw [graph1Rename] at hej
  exact ChildValuesProof.unary n (raw.relabel j) (child.relabel j) (d.relabel j) deps values hgj
    (ChildrenProof.unary ordinary (raw.relabel j) z (metadata.relabel j) (child.relabel j) deps hcj hd) hd hv hej

theorem resultRename {beta : Type} (n : Nat) (raw child out : OTerm alpha) (j : alpha → beta) :
    (Targets.unaryResult n raw child out).relabel j = Targets.unaryResult n (raw.relabel j) (child.relabel j) (out.relabel j) := by
  change (Targets.invalidResult n raw out ⊔ (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓ UnarySyntaxProof.block n child out)).relabel j = _
  simp only [Targets.invalidResult,LeafProof.orRename,conjunctionRename,graph1Rename,
    eqnRelabel,GuardedSourceSyntaxProof.numeralRename,UnarySyntaxProof.blockRename]
  rfl

theorem forward (ordinary : Bool) (n : Nat) (raw metadata child out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 (constructor ordinary) raw metadata child)))
    (ho : Nonempty (Derivation body Delta (graph1 (depth n) out raw))) :
    Nonempty (Derivation body Delta (Targets.unaryResult n raw child out)) := by
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
    rw [graph2Rename] at hcj
    have hoj := renameInto ho j Theta hj
    rw [graph1Rename] at hoj
    apply programCases (depth n) ![child.relabel j]
    intro gamma k Xi d hk hd
    simp only [consTermRename,emptyRename] at hd
    rw [resultRename]
    have hck := renameInto hcj k Xi hk
    rw [graph2Rename] at hck
    have hgk := renameInto hg k Xi hk
    simp only [graph1Rename,sucRelabel,zRelabel] at hgk
    have hok := renameInto hoj k Xi hk
    rw [graph1Rename] at hok
    have he := valueUnique (depth n) ((out.relabel j).relabel k) (suc d) ![(raw.relabel j).relabel k] hok
      (value ordinary n ((raw.relabel j).relabel k) ((metadata.relabel j).relabel k) ((child.relabel j).relabel k) d hck hgk hd)
    have hb := UnarySyntaxProof.introduce n ((child.relabel j).relabel k) ((out.relabel j).relabel k) ![d] (andIntro hd he)
    obtain ⟨h⟩ := andIntro hgk hb
    exact ⟨orRight h⟩

theorem backward (ordinary : Bool) (n : Nat) (raw metadata child out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 (constructor ordinary) raw metadata child)))
    (hw : Nonempty (Derivation body Delta (Targets.unaryResult n raw child out))) :
    Nonempty (Derivation body Delta (graph1 (depth n) out raw)) := by
  let L := Targets.invalidResult n raw out
  let R := graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓ UnarySyntaxProof.block n child out
  have hl : Nonempty (Derivation body (L :: Delta) L) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hr : Nonempty (Derivation body (R :: Delta) R) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨el⟩ := andRight hl
  obtain ⟨vl⟩ := outputTransport (depth n) z out ![raw] ⟨symm el⟩ (ValueProof.malformedValue n raw (andLeft hl))
  have vr : Nonempty (Derivation body (R :: Delta) (graph1 (depth n) out raw)) := by
    apply UnarySyntaxProof.cases n child out _ (andRight hr)
    intro beta j Theta ys hj hf
    rw [graph1Rename]
    have hcj := renameInto (withHyp hc R) j Theta hj
    rw [graph2Rename] at hcj
    have hgj := renameInto (andLeft hr) j Theta hj
    simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hgj
    obtain ⟨he⟩ := andRight hf
    exact outputTransport (depth n) (suc (ys 0)) (out.relabel j) ![raw.relabel j] ⟨symm he⟩
      (value ordinary n (raw.relabel j) (metadata.relabel j) (child.relabel j) (ys 0) hcj hgj (andLeft hf))
  obtain ⟨vr⟩ := vr
  obtain ⟨hw⟩ := hw
  exact ⟨InternalBetaTotalityProof.disjunctionElimination hw
    (Derivation.implicationIntroduction vl) (Derivation.implicationIntroduction vr)⟩

theorem internalLambda : Targets.InternalLambda := by
  intro n body alpha Delta raw out typ child hc
  exact ⟨forward false n raw typ child out hc,backward false n raw typ child out hc⟩

theorem internalOrdinary : Targets.InternalOrdinary := by
  intro n body alpha Delta raw out head child hc
  exact ⟨forward true n raw head child out hc,backward true n raw head child out hc⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.UnaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.UnaryProof
