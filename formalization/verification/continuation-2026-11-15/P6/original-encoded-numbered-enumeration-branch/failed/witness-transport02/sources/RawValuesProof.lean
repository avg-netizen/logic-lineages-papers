module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapIntroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapElimProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapImageEliminationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.ProductsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.TupleProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.RawValuesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open InternalTagArithmeticSyntaxProof (eqn z)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def fields (a b c d e f k h t base ts extra : OTerm alpha) : Formula alpha :=
  graph2 contains (numeral 1) a k ⊓ graph2 contains (numeral 1) b h ⊓
  graph2 contains (numeral 1) c t ⊓ graph2 contains (numeral 1) d base ⊓
  graph2 contains (numeral 1) e ts ⊓ graph2 contains (numeral 1) f extra

theorem forward (a b c d e f r56 r456 r3456 r23456 r123456 k h t base ts extra p56 p456 p3456 p23456 p123456 out code : OTerm alpha)
    (hg56 : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross r56 e f)))
    (hp56 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p56 ts extra)))
    (hg456 : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross r456 d r56)))
    (hp456 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p456 base p56)))
    (hg3456 : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross r3456 c r456)))
    (hp3456 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p3456 t p456)))
    (hg23456 : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross r23456 b r3456)))
    (hp23456 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p23456 h p3456)))
    (hg123456 : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross r123456 a r23456)))
    (hp123456 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p123456 k p23456)))
    (hv : Nonempty (Derivation body Delta (graph1 (InternalListMap.map OriginalNumberedEnumerationBranch.tagPayload) out r123456)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code (numeral 5) p123456)))
    (hm : Nonempty (Derivation body Delta (fields a b c d e f k h t base ts extra))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  have hma := (andLeft (andLeft (andLeft (andLeft (andLeft hm)))))
  have hmb := (andRight (andLeft (andLeft (andLeft (andLeft hm)))))
  have hmc := (andRight (andLeft (andLeft (andLeft hm))))
  have hmd := (andRight (andLeft (andLeft hm)))
  have hme := (andRight (andLeft hm))
  have hmf := (andRight hm)
  have hprod := ProductsProof.introduction a b c d e f r56 r456 r3456 r23456 r123456 k h t base ts extra p56 p456 p3456 p23456 p123456 hg56 hp56 hg456 hp456 hg3456 hp3456 hg23456 hp23456 hg123456 hp123456 hma hmb hmc hmd hme hmf
  exact MapIntroProof.introduce OriginalNumberedEnumerationBranch.tagPayload r123456 z out code z p123456 hv hprod (TupleProof.tagValue p123456 code hc)

theorem backward (a b c d e f r56 r456 r3456 r23456 r123456 k h t base ts extra p56 p456 p3456 p23456 p123456 out code : OTerm alpha)
    (hg56 : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross r56 e f)))
    (hp56 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p56 ts extra)))
    (hg456 : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross r456 d r56)))
    (hp456 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p456 base p56)))
    (hg3456 : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross r3456 c r456)))
    (hp3456 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p3456 t p456)))
    (hg23456 : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross r23456 b r3456)))
    (hp23456 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p23456 h p3456)))
    (hg123456 : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross r123456 a r23456)))
    (hp123456 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p123456 k p23456)))
    (hv : Nonempty (Derivation body Delta (graph1 (InternalListMap.map OriginalNumberedEnumerationBranch.tagPayload) out r123456)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code (numeral 5) p123456)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) :
    Nonempty (Derivation body Delta (fields a b c d e f k h t base ts extra)) := by
  have hi := MapElimProof.recover OriginalNumberedEnumerationBranch.tagPayload r123456 out code hv hm
  apply MapImageEliminationProof.cases OriginalNumberedEnumerationBranch.tagPayload r123456 code _ hi
  intro beta j Theta observed hj hmem htag
  simp only [fields,conjunctionRename,graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hg56j := InternalGraphCompositionFunctionalityProof.renameInto hg56 j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hg56j
  have hp56j := InternalGraphCompositionFunctionalityProof.renameInto hp56 j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hp56j
  have hg456j := InternalGraphCompositionFunctionalityProof.renameInto hg456 j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hg456j
  have hp456j := InternalGraphCompositionFunctionalityProof.renameInto hp456 j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hp456j
  have hg3456j := InternalGraphCompositionFunctionalityProof.renameInto hg3456 j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hg3456j
  have hp3456j := InternalGraphCompositionFunctionalityProof.renameInto hp3456 j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hp3456j
  have hg23456j := InternalGraphCompositionFunctionalityProof.renameInto hg23456 j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hg23456j
  have hp23456j := InternalGraphCompositionFunctionalityProof.renameInto hp23456 j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hp23456j
  have hg123456j := InternalGraphCompositionFunctionalityProof.renameInto hg123456 j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hg123456j
  have hp123456j := InternalGraphCompositionFunctionalityProof.renameInto hp123456 j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hp123456j
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hcj
  have hpair := TupleProof.tagRecover observed (code.relabel j) htag
  have heq := valueUnique InternalUnpair.right observed (p123456.relabel j) ![code.relabel j]
    (pairRight (code.relabel j) (numeral 5) observed hpair)
    (pairRight (code.relabel j) (numeral 5) (p123456.relabel j) hcj)
  have hmem' := InternalApplicationValidityStackAppendRunProof.rightTransport contains (numeral 1)
    (r123456.relabel j) observed (p123456.relabel j) heq hmem
  exact ProductsProof.elimination (a.relabel j) (b.relabel j) (c.relabel j) (d.relabel j) (e.relabel j) (f.relabel j) (r56.relabel j) (r456.relabel j) (r3456.relabel j) (r23456.relabel j) (r123456.relabel j) (k.relabel j) (h.relabel j) (t.relabel j) (base.relabel j) (ts.relabel j) (extra.relabel j) (p56.relabel j) (p456.relabel j) (p3456.relabel j) (p23456.relabel j) (p123456.relabel j)
    hg56j hp56j hg456j hp456j hg3456j hp3456j hg23456j hp23456j hg123456j hp123456j hmem'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.RawValuesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.RawValuesProof
