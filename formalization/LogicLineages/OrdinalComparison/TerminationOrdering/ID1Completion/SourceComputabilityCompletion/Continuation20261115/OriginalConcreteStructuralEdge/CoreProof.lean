module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.CoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalAcceptanceBranchProof InternalTagArithmeticSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalTagArithmeticSyntaxProof (eqn)

open Continuation20261114
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqnRelabel)
open InternalRecursionGraphStepSyntaxProof

def guards (n : Nat) (codeA codeB ctx : OTerm alpha) : Formula alpha :=
  graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 1) ctx ⊓
    (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) codeA ⊓
     graph1 (OriginalCodeValidityGuard.check n) (numeral 1) codeB)
def relation (n : Nat) (arity : Fin n → Nat) (codeA codeB ctx : OTerm alpha) : Formula alpha :=
  guards n codeA codeB ctx ⊓ graph3 (atContext n arity) (numeral 1) codeA codeB ctx

theorem relationRename (n : Nat) (arity : Fin n → Nat) (a b ctx : OTerm alpha) {beta : Type} (j : alpha → beta) :
    (relation n arity a b ctx).relabel j = relation n arity (a.relabel j) (b.relabel j) (ctx.relabel j) := by
  simp only [relation,guards,conjunctionRename,graph1Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename]

theorem atWitnesses (n : Nat) (arity : Fin n → Nat)
    (source target param tyA codeA tyB codeB ctx rest win table node : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source tyA codeA)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target tyB codeB)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ctx rest)))
    (hw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ctx win table)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node codeA codeB))) :
    (Nonempty (Derivation body Delta (graph3 (structural n arity) (numeral 1) source target param)) ↔
     Nonempty (Derivation body Delta (relation n arity codeA codeB ctx))) := by
  have hnode := SupportProof.nodeAt source target param tyA codeA tyB codeB node hs ht hn
  constructor
  · intro h
    have hv := SupportProof.guardNecessary n arity source target param h
    have hg := (OriginalStructuralDecoderSuppliers.ValidProof.internalValid n body alpha Delta
      source target param tyA codeA tyB codeB ctx rest hs ht hp).mp hv
    have hk := OriginalStructuralDecoderSuppliers.WindowProof.positiveAt n param ctx rest win table hp hw (andLeft hg)
    have he := (InstalledExchangeRecursor.InternalProof.internalFactor body alpha Delta
      (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n) (OriginalDecodedLayerCalibration.layer n arity)
      (OriginalStructuralDecoderSuppliers.valid n) (OriginalStructuralDecoderSuppliers.window n)
      source target param node win (numeral 1) hv hnode hk).mp h
    exact andIntro hg ((SupportProof.atContextFactor n arity codeA codeB ctx win table node (numeral 1) hw hn).mpr he)
  · intro h
    have hg := andLeft h
    have hv := (OriginalStructuralDecoderSuppliers.ValidProof.internalValid n body alpha Delta
      source target param tyA codeA tyB codeB ctx rest hs ht hp).mpr hg
    have hk := OriginalStructuralDecoderSuppliers.WindowProof.positiveAt n param ctx rest win table hp hw (andLeft hg)
    have he := (SupportProof.atContextFactor n arity codeA codeB ctx win table node (numeral 1) hw hn).mp (andRight h)
    exact (InstalledExchangeRecursor.InternalProof.internalFactor body alpha Delta
      (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n) (OriginalDecodedLayerCalibration.layer n arity)
      (OriginalStructuralDecoderSuppliers.valid n) (OriginalStructuralDecoderSuppliers.window n)
      source target param node win (numeral 1) hv hnode hk).mpr he

theorem atWindowForward (n : Nat) (arity : Fin n → Nat) (source target param tyA codeA tyB codeB ctx rest win table : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source tyA codeA)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target tyB codeB)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ctx rest)))
    (hw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ctx win table)))
    (h : Nonempty (Derivation body Delta (graph3 (structural n arity) (numeral 1) source target param))) :
    Nonempty (Derivation body Delta (relation n arity codeA codeB ctx)) := by
  apply InternalAcceptanceSupportProof.programCases InternalPairing.pairing (Fin.cons codeA (Fin.cons codeB Fin.elim0)) _
  intro beta j Theta node hj hn
  simp only [consTermRename,emptyRename] at hn
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,relationRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,relationRename] at htj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,relationRename] at hpj
  have hwj := InternalGraphCompositionFunctionalityProof.renameInto hw j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,relationRename] at hwj
  have hj := InternalGraphCompositionFunctionalityProof.renameInto h j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,relationRename] at hj
  exact (atWitnesses n arity (source.relabel j) (target.relabel j) (param.relabel j) (tyA.relabel j) (codeA.relabel j) (tyB.relabel j) (codeB.relabel j) (ctx.relabel j) (rest.relabel j) (win.relabel j) (table.relabel j) node hsj htj hpj hwj hn).mp hj

theorem atWindowBackward (n : Nat) (arity : Fin n → Nat) (source target param tyA codeA tyB codeB ctx rest win table : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source tyA codeA)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target tyB codeB)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ctx rest)))
    (hw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ctx win table)))
    (h : Nonempty (Derivation body Delta (relation n arity codeA codeB ctx))) :
    Nonempty (Derivation body Delta (graph3 (structural n arity) (numeral 1) source target param)) := by
  apply InternalAcceptanceSupportProof.programCases InternalPairing.pairing (Fin.cons codeA (Fin.cons codeB Fin.elim0)) _
  intro beta j Theta node hj hn
  simp only [consTermRename,emptyRename] at hn
  simp only [graph3Rename,GuardedSourceSyntaxProof.numeralRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,relationRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,relationRename] at htj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,relationRename] at hpj
  have hwj := InternalGraphCompositionFunctionalityProof.renameInto hw j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,relationRename] at hwj
  have hj := InternalGraphCompositionFunctionalityProof.renameInto h j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,relationRename] at hj
  exact (atWitnesses n arity (source.relabel j) (target.relabel j) (param.relabel j) (tyA.relabel j) (codeA.relabel j) (tyB.relabel j) (codeB.relabel j) (ctx.relabel j) (rest.relabel j) (win.relabel j) (table.relabel j) node hsj htj hpj hwj hn).mpr hj

theorem structuralForward (n : Nat) (arity : Fin n → Nat) (source target param tyA codeA tyB codeB ctx rest : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source tyA codeA)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target tyB codeB)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ctx rest)))
    (h : Nonempty (Derivation body Delta (graph3 (structural n arity) (numeral 1) source target param))) :
    Nonempty (Derivation body Delta (relation n arity codeA codeB ctx)) := by
  apply OriginalDecodedRank.SupportProof.pairCases ctx _
  intro beta j Theta win table hj hw
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,relationRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,relationRename] at htj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,relationRename] at hpj
  have hj := InternalGraphCompositionFunctionalityProof.renameInto h j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,relationRename] at hj
  exact atWindowForward n arity (source.relabel j) (target.relabel j) (param.relabel j) (tyA.relabel j) (codeA.relabel j) (tyB.relabel j) (codeB.relabel j) (ctx.relabel j) (rest.relabel j) win table hsj htj hpj hw hj

theorem structuralBackward (n : Nat) (arity : Fin n → Nat) (source target param tyA codeA tyB codeB ctx rest : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source tyA codeA)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target tyB codeB)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ctx rest)))
    (h : Nonempty (Derivation body Delta (relation n arity codeA codeB ctx))) :
    Nonempty (Derivation body Delta (graph3 (structural n arity) (numeral 1) source target param)) := by
  apply OriginalDecodedRank.SupportProof.pairCases ctx _
  intro beta j Theta win table hj hw
  simp only [graph3Rename,GuardedSourceSyntaxProof.numeralRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,relationRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,relationRename] at htj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,relationRename] at hpj
  have hj := InternalGraphCompositionFunctionalityProof.renameInto h j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,relationRename] at hj
  exact atWindowBackward n arity (source.relabel j) (target.relabel j) (param.relabel j) (tyA.relabel j) (codeA.relabel j) (tyB.relabel j) (codeB.relabel j) (ctx.relabel j) (rest.relabel j) win table hsj htj hpj hw hj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.CoreProof
