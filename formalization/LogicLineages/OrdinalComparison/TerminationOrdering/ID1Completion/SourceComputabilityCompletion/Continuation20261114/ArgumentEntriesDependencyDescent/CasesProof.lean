module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesDependencyDescent.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesDependencyDescent.CasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (eqnRelabel sucRelabel zRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open InternalOriginalPairingOrderArithmeticProof (strictTransport)
open OriginalRawSyntaxTransportInternalConstructorBoundsProof
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open SupportProof

theorem unary2 (raw deps child first listCode : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 1) raw)))
    (hd : Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children deps raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hfirst : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) first raw)))
    (hlistCode : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode first z)))
    : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)) := by
  exact SupportProof.unaryAt raw deps child first listCode ha hd hm hfirst hlistCode

theorem unary1 (raw deps child first : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 1) raw)))
    (hd : Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children deps raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hfirst : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) first raw)))
    : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons first (Fin.cons z (Fin.elim0))) _
  intro beta j Theta listCode hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [strictRename]
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at haj
  have hdj := renameInto hd j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hfirstj := renameInto hfirst j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hfirstj
  exact unary2 (raw.relabel j) (deps.relabel j) (child.relabel j) (first.relabel j) listCode haj hdj hmj hfirstj hx

theorem unary (raw deps child : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 1) raw)))
    (hd : Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children deps raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)) := by
  apply programCases (OriginalRawSyntaxTransport.firstOf (.projection 0)) (Fin.cons raw (Fin.elim0)) _
  intro beta j Theta first hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [strictRename]
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at haj
  have hdj := renameInto hd j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  exact unary1 (raw.relabel j) (deps.relabel j) (child.relabel j) first haj hdj hmj hx

theorem binary4 (raw deps child first second rest listCode : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 2) raw)))
    (hd : Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children deps raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hfirst : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) first raw)))
    (hsecond : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.secondOf (.projection 0)) second raw)))
    (hrest : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest second z)))
    (hlistCode : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode first rest)))
    : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)) := by
  exact SupportProof.binaryAt raw deps child first second rest listCode ha hd hm hfirst hsecond hrest hlistCode

theorem binary3 (raw deps child first second rest : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 2) raw)))
    (hd : Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children deps raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hfirst : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) first raw)))
    (hsecond : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.secondOf (.projection 0)) second raw)))
    (hrest : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest second z)))
    : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons first (Fin.cons rest (Fin.elim0))) _
  intro beta j Theta listCode hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [strictRename]
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at haj
  have hdj := renameInto hd j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hfirstj := renameInto hfirst j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hfirstj
  have hsecondj := renameInto hsecond j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsecondj
  have hrestj := renameInto hrest j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrestj
  exact binary4 (raw.relabel j) (deps.relabel j) (child.relabel j) (first.relabel j) (second.relabel j) (rest.relabel j) listCode haj hdj hmj hfirstj hsecondj hrestj hx

theorem binary2 (raw deps child first second : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 2) raw)))
    (hd : Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children deps raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hfirst : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) first raw)))
    (hsecond : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.secondOf (.projection 0)) second raw)))
    : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons second (Fin.cons z (Fin.elim0))) _
  intro beta j Theta rest hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [strictRename]
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at haj
  have hdj := renameInto hd j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hfirstj := renameInto hfirst j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hfirstj
  have hsecondj := renameInto hsecond j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsecondj
  exact binary3 (raw.relabel j) (deps.relabel j) (child.relabel j) (first.relabel j) (second.relabel j) rest haj hdj hmj hfirstj hsecondj hx

theorem binary1 (raw deps child first : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 2) raw)))
    (hd : Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children deps raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hfirst : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) first raw)))
    : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)) := by
  apply programCases (OriginalRawSyntaxTransport.secondOf (.projection 0)) (Fin.cons raw (Fin.elim0)) _
  intro beta j Theta second hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [strictRename]
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at haj
  have hdj := renameInto hd j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hfirstj := renameInto hfirst j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hfirstj
  exact binary2 (raw.relabel j) (deps.relabel j) (child.relabel j) (first.relabel j) second haj hdj hmj hfirstj hx

theorem binary (raw deps child : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 2) raw)))
    (hd : Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children deps raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)) := by
  apply programCases (OriginalRawSyntaxTransport.firstOf (.projection 0)) (Fin.cons raw (Fin.elim0)) _
  intro beta j Theta first hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [strictRename]
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at haj
  have hdj := renameInto hd j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  exact binary1 (raw.relabel j) (deps.relabel j) (child.relabel j) first haj hdj hmj hx

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesDependencyDescent.CasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesDependencyDescent.CasesProof
