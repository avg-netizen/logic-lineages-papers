module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ChildrenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.LeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalRecursionClosureSyntaxProof (conjunctionRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalQuotientComparisonProof (orLeft orRight)
open SourceComputabilityFormulaSupportProof (numeral)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem orRename {beta : Type} (p q : Formula alpha) (j : alpha → beta) :
    (p ⊔ q).relabel j = p.relabel j ⊔ q.relabel j := rfl

theorem leafRename {beta : Type} (n : Nat) (raw out : OTerm alpha) (j : alpha → beta) :
    (Targets.leafResult n raw out).relabel j = Targets.leafResult n (raw.relabel j) (out.relabel j) := by
  simp only [Targets.leafResult,Targets.invalidResult,orRename,conjunctionRename,
    graph1Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename]

theorem forward (n : Nat) (raw out : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 dependency z raw z)))
    (ho : Nonempty (Derivation body Delta (graph1 (depth n) out raw))) :
    Nonempty (Derivation body Delta (Targets.leafResult n raw out)) := by
  apply OriginalCodeBoundsRecursion.CasesProof.guardCases n raw
  · intro beta j Theta hj hg
    rw [leafRename]
    have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
    rw [graph1Rename] at hoj
    have he := valueUnique (depth n) (out.relabel j) z ![raw.relabel j] hoj (ValueProof.malformedValue n (raw.relabel j) hg)
    obtain ⟨h⟩ := andIntro hg he
    exact ⟨orLeft h⟩
  · intro beta j Theta hj hg
    rw [leafRename]
    have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
    rw [graph1Rename] at hoj
    have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
    simp only [graph2Rename,zRelabel] at hdj
    have he := valueUnique (depth n) (out.relabel j) (suc z) ![raw.relabel j] hoj (ValueProof.leaf n (raw.relabel j) hg hdj)
    obtain ⟨h⟩ := andIntro hg he
    exact ⟨orRight h⟩

theorem backward (n : Nat) (raw out : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 dependency z raw z)))
    (hw : Nonempty (Derivation body Delta (Targets.leafResult n raw out))) :
    Nonempty (Derivation body Delta (graph1 (depth n) out raw)) := by
  let L := Targets.invalidResult n raw out
  let R := graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓ eqn out (numeral 1)
  have hl : Nonempty (Derivation body (L :: Delta) L) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hr : Nonempty (Derivation body (R :: Delta) R) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨el⟩ := andRight hl
  obtain ⟨er⟩ := andRight hr
  obtain ⟨vl⟩ := outputTransport (depth n) z out ![raw] ⟨symm el⟩ (ValueProof.malformedValue n raw (andLeft hl))
  obtain ⟨vr⟩ := outputTransport (depth n) (suc z) out ![raw] ⟨symm er⟩ (ValueProof.leaf n raw (andLeft hr) (withHyp hd R))
  obtain ⟨hw⟩ := hw
  exact ⟨InternalBetaTotalityProof.disjunctionElimination hw
    (Derivation.implicationIntroduction vl) (Derivation.implicationIntroduction vr)⟩

theorem internalVariable : Targets.InternalVariable := by
  intro n body alpha Delta raw out index hc
  have hd := ChildrenProof.variableLeaf raw z index hc
  exact ⟨forward n raw out hd,backward n raw out hd⟩

theorem internalBottom : Targets.InternalBottom := by
  intro n body alpha Delta raw out typ hc
  have hd := ChildrenProof.bottom raw z typ hc
  exact ⟨forward n raw out hd,backward n raw out hd⟩

theorem internalNil : Targets.InternalNil := by
  intro n body alpha Delta raw out  hc
  have hd := ChildrenProof.nil raw z hc
  exact ⟨forward n raw out hd,backward n raw out hd⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.LeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.LeafProof
