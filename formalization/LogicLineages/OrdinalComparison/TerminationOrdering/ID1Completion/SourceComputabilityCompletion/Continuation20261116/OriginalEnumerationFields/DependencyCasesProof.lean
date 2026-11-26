module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.DependencyDescentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.DependencyCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalConstructorArityCasesProof
open Continuation20261114.ArgumentEntriesDependencyDescent.SupportProof (strictRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem unary3 (key code bound param deps child childRank first firstKeyValue listCode : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 1) code)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hrank : Nonempty (Derivation body Delta (graph2 rank childRank child param)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first code)))
    (hfk : Nonempty (Derivation body Delta (graph2 (firstKey) firstKeyValue key param)))
    (hc : Nonempty (Derivation body Delta (graph2 (InternalListCodec.consCode) listCode firstKeyValue z)))
    : Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank code)) := by
  exact DependencyDescentProof.unaryAt key code bound param deps child childRank first firstKeyValue listCode hk ha hd hm hrank hf hfk hc

theorem unary2 (key code bound param deps child childRank first firstKeyValue : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 1) code)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hrank : Nonempty (Derivation body Delta (graph2 rank childRank child param)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first code)))
    (hfk : Nonempty (Derivation body Delta (graph2 (firstKey) firstKeyValue key param)))
    : Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank code)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons firstKeyValue (Fin.cons z Fin.elim0)) _
  intro beta j Theta listCode hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [strictRename]
  have hkj := renameInto hk j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hkj
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at haj
  have hdj := renameInto hd j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hrankj := renameInto hrank j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrankj
  have hfj := renameInto hf j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hfj
  have hfkj := renameInto hfk j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hfkj
  exact unary3 (key.relabel j) (code.relabel j) (bound.relabel j) (param.relabel j) (deps.relabel j) (child.relabel j) (childRank.relabel j) (first.relabel j) (firstKeyValue.relabel j) listCode hkj haj hdj hmj hrankj hfj hfkj hx

theorem unary1 (key code bound param deps child childRank first : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 1) code)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hrank : Nonempty (Derivation body Delta (graph2 rank childRank child param)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first code)))
    : Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank code)) := by
  apply programCases (firstKey) (Fin.cons key (Fin.cons param Fin.elim0)) _
  intro beta j Theta firstKeyValue hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [strictRename]
  have hkj := renameInto hk j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hkj
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at haj
  have hdj := renameInto hd j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hrankj := renameInto hrank j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrankj
  have hfj := renameInto hf j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hfj
  exact unary2 (key.relabel j) (code.relabel j) (bound.relabel j) (param.relabel j) (deps.relabel j) (child.relabel j) (childRank.relabel j) (first.relabel j) firstKeyValue hkj haj hdj hmj hrankj hfj hx

theorem unary (key code bound param deps child childRank : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 1) code)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hrank : Nonempty (Derivation body Delta (graph2 rank childRank child param)))
    : Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank code)) := by
  apply programCases (firstOf (.projection 0)) (Fin.cons code Fin.elim0) _
  intro beta j Theta first hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [strictRename]
  have hkj := renameInto hk j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hkj
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at haj
  have hdj := renameInto hd j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hrankj := renameInto hrank j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrankj
  exact unary1 (key.relabel j) (code.relabel j) (bound.relabel j) (param.relabel j) (deps.relabel j) (child.relabel j) (childRank.relabel j) first hkj haj hdj hmj hrankj hx

theorem binary6 (key code bound param deps child childRank first second firstKeyValue secondKeyValue rest listCode : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) code)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hrank : Nonempty (Derivation body Delta (graph2 rank childRank child param)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first code)))
    (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second code)))
    (hfk : Nonempty (Derivation body Delta (graph2 (firstKey) firstKeyValue key param)))
    (hsk : Nonempty (Derivation body Delta (graph2 (secondKey) secondKeyValue key param)))
    (hr : Nonempty (Derivation body Delta (graph2 (InternalListCodec.consCode) rest secondKeyValue z)))
    (hc : Nonempty (Derivation body Delta (graph2 (InternalListCodec.consCode) listCode firstKeyValue rest)))
    : Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank code)) := by
  exact DependencyDescentProof.binaryAt key code bound param deps child childRank first second firstKeyValue secondKeyValue rest listCode hk ha hd hm hrank hf hs hfk hsk hr hc

theorem binary5 (key code bound param deps child childRank first second firstKeyValue secondKeyValue rest : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) code)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hrank : Nonempty (Derivation body Delta (graph2 rank childRank child param)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first code)))
    (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second code)))
    (hfk : Nonempty (Derivation body Delta (graph2 (firstKey) firstKeyValue key param)))
    (hsk : Nonempty (Derivation body Delta (graph2 (secondKey) secondKeyValue key param)))
    (hr : Nonempty (Derivation body Delta (graph2 (InternalListCodec.consCode) rest secondKeyValue z)))
    : Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank code)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons firstKeyValue (Fin.cons rest Fin.elim0)) _
  intro beta j Theta listCode hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [strictRename]
  have hkj := renameInto hk j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hkj
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at haj
  have hdj := renameInto hd j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hrankj := renameInto hrank j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrankj
  have hfj := renameInto hf j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hfj
  have hsj := renameInto hs j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have hfkj := renameInto hfk j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hfkj
  have hskj := renameInto hsk j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hskj
  have hrj := renameInto hr j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrj
  exact binary6 (key.relabel j) (code.relabel j) (bound.relabel j) (param.relabel j) (deps.relabel j) (child.relabel j) (childRank.relabel j) (first.relabel j) (second.relabel j) (firstKeyValue.relabel j) (secondKeyValue.relabel j) (rest.relabel j) listCode hkj haj hdj hmj hrankj hfj hsj hfkj hskj hrj hx

theorem binary4 (key code bound param deps child childRank first second firstKeyValue secondKeyValue : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) code)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hrank : Nonempty (Derivation body Delta (graph2 rank childRank child param)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first code)))
    (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second code)))
    (hfk : Nonempty (Derivation body Delta (graph2 (firstKey) firstKeyValue key param)))
    (hsk : Nonempty (Derivation body Delta (graph2 (secondKey) secondKeyValue key param)))
    : Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank code)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons secondKeyValue (Fin.cons z Fin.elim0)) _
  intro beta j Theta rest hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [strictRename]
  have hkj := renameInto hk j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hkj
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at haj
  have hdj := renameInto hd j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hrankj := renameInto hrank j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrankj
  have hfj := renameInto hf j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hfj
  have hsj := renameInto hs j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have hfkj := renameInto hfk j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hfkj
  have hskj := renameInto hsk j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hskj
  exact binary5 (key.relabel j) (code.relabel j) (bound.relabel j) (param.relabel j) (deps.relabel j) (child.relabel j) (childRank.relabel j) (first.relabel j) (second.relabel j) (firstKeyValue.relabel j) (secondKeyValue.relabel j) rest hkj haj hdj hmj hrankj hfj hsj hfkj hskj hx

theorem binary3 (key code bound param deps child childRank first second firstKeyValue : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) code)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hrank : Nonempty (Derivation body Delta (graph2 rank childRank child param)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first code)))
    (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second code)))
    (hfk : Nonempty (Derivation body Delta (graph2 (firstKey) firstKeyValue key param)))
    : Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank code)) := by
  apply programCases (secondKey) (Fin.cons key (Fin.cons param Fin.elim0)) _
  intro beta j Theta secondKeyValue hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [strictRename]
  have hkj := renameInto hk j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hkj
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at haj
  have hdj := renameInto hd j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hrankj := renameInto hrank j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrankj
  have hfj := renameInto hf j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hfj
  have hsj := renameInto hs j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have hfkj := renameInto hfk j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hfkj
  exact binary4 (key.relabel j) (code.relabel j) (bound.relabel j) (param.relabel j) (deps.relabel j) (child.relabel j) (childRank.relabel j) (first.relabel j) (second.relabel j) (firstKeyValue.relabel j) secondKeyValue hkj haj hdj hmj hrankj hfj hsj hfkj hx

theorem binary2 (key code bound param deps child childRank first second : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) code)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hrank : Nonempty (Derivation body Delta (graph2 rank childRank child param)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first code)))
    (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second code)))
    : Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank code)) := by
  apply programCases (firstKey) (Fin.cons key (Fin.cons param Fin.elim0)) _
  intro beta j Theta firstKeyValue hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [strictRename]
  have hkj := renameInto hk j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hkj
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at haj
  have hdj := renameInto hd j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hrankj := renameInto hrank j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrankj
  have hfj := renameInto hf j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hfj
  have hsj := renameInto hs j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  exact binary3 (key.relabel j) (code.relabel j) (bound.relabel j) (param.relabel j) (deps.relabel j) (child.relabel j) (childRank.relabel j) (first.relabel j) (second.relabel j) firstKeyValue hkj haj hdj hmj hrankj hfj hsj hx

theorem binary1 (key code bound param deps child childRank first : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) code)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hrank : Nonempty (Derivation body Delta (graph2 rank childRank child param)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first code)))
    : Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank code)) := by
  apply programCases (secondOf (.projection 0)) (Fin.cons code Fin.elim0) _
  intro beta j Theta second hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [strictRename]
  have hkj := renameInto hk j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hkj
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at haj
  have hdj := renameInto hd j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hrankj := renameInto hrank j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrankj
  have hfj := renameInto hf j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hfj
  exact binary2 (key.relabel j) (code.relabel j) (bound.relabel j) (param.relabel j) (deps.relabel j) (child.relabel j) (childRank.relabel j) (first.relabel j) second hkj haj hdj hmj hrankj hfj hx

theorem binary (key code bound param deps child childRank : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) code)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hrank : Nonempty (Derivation body Delta (graph2 rank childRank child param)))
    : Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank code)) := by
  apply programCases (firstOf (.projection 0)) (Fin.cons code Fin.elim0) _
  intro beta j Theta first hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [strictRename]
  have hkj := renameInto hk j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hkj
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at haj
  have hdj := renameInto hd j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hrankj := renameInto hrank j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrankj
  exact binary1 (key.relabel j) (code.relabel j) (bound.relabel j) (param.relabel j) (deps.relabel j) (child.relabel j) (childRank.relabel j) first hkj haj hdj hmj hrankj hx
theorem pairedDescent (key code bound param deps child childRank : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hrank : Nonempty (Derivation body Delta (graph2 rank childRank child param))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank code)) := by
  apply arityCases code _
  · intro beta j Theta hj ha
    rw [strictRename]
    have hkj := renameInto hk j Theta hj
    simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hkj
    have hdj := renameInto hd j Theta hj
    simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hdj
    have hmj := renameInto hm j Theta hj
    simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
    have hrankj := renameInto hrank j Theta hj
    simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hrankj
    exact DependencyDescentProof.zeroCase (key.relabel j) (param.relabel j) (deps.relabel j) (child.relabel j) (childRank.relabel j) (code.relabel j) (bound.relabel j) hkj ha hdj hmj
  · intro beta j Theta hj ha
    rw [strictRename]
    have hkj := renameInto hk j Theta hj
    simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hkj
    have hdj := renameInto hd j Theta hj
    simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hdj
    have hmj := renameInto hm j Theta hj
    simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
    have hrankj := renameInto hrank j Theta hj
    simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hrankj
    exact unary (key.relabel j) (code.relabel j) (bound.relabel j) (param.relabel j) (deps.relabel j) (child.relabel j) (childRank.relabel j) hkj ha hdj hmj hrankj
  · intro beta j Theta hj ha
    rw [strictRename]
    have hkj := renameInto hk j Theta hj
    simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hkj
    have hdj := renameInto hd j Theta hj
    simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hdj
    have hmj := renameInto hm j Theta hj
    simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
    have hrankj := renameInto hrank j Theta hj
    simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hrankj
    exact binary (key.relabel j) (code.relabel j) (bound.relabel j) (param.relabel j) (deps.relabel j) (child.relabel j) (childRank.relabel j) hkj ha hdj hmj hrankj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.DependencyCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.DependencyCasesProof
