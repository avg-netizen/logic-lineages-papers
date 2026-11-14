module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralNumberedLayer.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralNumberedLayer.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ResultStructuralFields.SupportProof (active)

def result {alpha : Type} (k l tau upsilon ts us extras otherExtras ef eg move base dest h0 h3 : OTerm alpha) : Formula alpha :=
  ((eqn k l ⊓ (eqn tau upsilon ⊓ eqn ts us)) ⊓
     (((eqn extras otherExtras ⊓ eqn move (numeral 1)) ⊔
       ((eqn ef eg ⊓ eqn extras otherExtras) ⊓ eqn h0 (numeral 1))) ⊔
      ((eqn ef eg ⊓ eqn base dest) ⊓ eqn h3 (numeral 1))))
theorem resultRename {alpha beta : Type} (k l tau upsilon ts us extras otherExtras ef eg move base dest h0 h3 : OTerm alpha) (j : alpha → beta) :
    (result k l tau upsilon ts us extras otherExtras ef eg move base dest h0 h3).relabel j =
      result (k.relabel j) (l.relabel j) (tau.relabel j) (upsilon.relabel j) (ts.relabel j) (us.relabel j) (extras.relabel j) (otherExtras.relabel j) (ef.relabel j) (eg.relabel j) (move.relabel j) (base.relabel j) (dest.relabel j) (h0.relabel j) (h3.relabel j) := by
  simp only [result,StructuralExchangeFields.InternalProof.andRename,
    StructuralExchangeFields.InternalProof.orRename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename]

theorem internalNumbered : Targets.InternalNumbered := by
  intro body alpha Delta U V node code param source target k l f g tau upsilon base dest ts us extras otherExtras ef eg move h0 t0 h1 t1 h2 t2 h3 t3
    hV hn hsource htarget hef heg hm hc0 hc1 hc2 hc3
  constructor
  · intro h
    change Nonempty (Derivation body Delta (result k l tau upsilon ts us extras otherExtras ef eg move base dest h0 h3))
    apply InternalGraphCompositionTotalityProof.supplyOutputs body 3 19
      (fun i => OrdinaryArithmetic.graphFormula (active U V i))
      (fun i => (InternalRecursionClosureProof.actualOriginalPrograms body 3 (active U V i)).1)
      alpha Delta ![node,code,param] _
    intro beta j Theta ys hj hys
    have hv : (fun i : Fin 3 => (![node,code,param] i).relabel j) =
        ![node.relabel j,code.relabel j,param.relabel j] := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
    rw [hv] at hys
    change ∀ i, Nonempty (Derivation body Theta
      (graph3 (active U V i) (ys i) (node.relabel j) (code.relabel j) (param.relabel j))) at hys
    have hVj := renameInto hV j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,programRename,GuardedSourceSyntaxProof.numeralRename] at hVj
    have hnj := renameInto hn j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,programRename,GuardedSourceSyntaxProof.numeralRename] at hnj
    have hsourcej := renameInto hsource j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,programRename,GuardedSourceSyntaxProof.numeralRename] at hsourcej
    have htargetj := renameInto htarget j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,programRename,GuardedSourceSyntaxProof.numeralRename] at htargetj
    have hefj := renameInto hef j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,programRename,GuardedSourceSyntaxProof.numeralRename] at hefj
    have hegj := renameInto heg j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,programRename,GuardedSourceSyntaxProof.numeralRename] at hegj
    have hmj := renameInto hm j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,programRename,GuardedSourceSyntaxProof.numeralRename] at hmj
    have hc0j := renameInto hc0 j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,programRename,GuardedSourceSyntaxProof.numeralRename] at hc0j
    have hc1j := renameInto hc1 j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,programRename,GuardedSourceSyntaxProof.numeralRename] at hc1j
    have hc2j := renameInto hc2 j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,programRename,GuardedSourceSyntaxProof.numeralRename] at hc2j
    have hc3j := renameInto hc3 j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,programRename,GuardedSourceSyntaxProof.numeralRename] at hc3j
    have hj := renameInto h j Theta hj
    simp only [graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hj
    have hf := SupportProof.atFields body beta Theta U V
      (node.relabel j) (code.relabel j) (param.relabel j) (source.relabel j) (target.relabel j) (k.relabel j) (l.relabel j) (f.relabel j) (g.relabel j) (tau.relabel j) (upsilon.relabel j) (base.relabel j) (dest.relabel j) (ts.relabel j) (us.relabel j) (extras.relabel j) (otherExtras.relabel j) (ef.relabel j) (eg.relabel j) (move.relabel j) (h0.relabel j) (t0.relabel j) (h1.relabel j) (t1.relabel j) (h2.relabel j) (t2.relabel j) (h3.relabel j) (t3.relabel j)
      hVj hnj hsourcej htargetj hefj hegj hmj hc0j hc1j hc2j hc3j ys hys
    simp only [resultRename]
    exact hf.mp hj
  · intro h
    change Nonempty (Derivation body Delta (result k l tau upsilon ts us extras otherExtras ef eg move base dest h0 h3)) at h
    apply InternalGraphCompositionTotalityProof.supplyOutputs body 3 19
      (fun i => OrdinaryArithmetic.graphFormula (active U V i))
      (fun i => (InternalRecursionClosureProof.actualOriginalPrograms body 3 (active U V i)).1)
      alpha Delta ![node,code,param] _
    intro beta j Theta ys hj hys
    have hv : (fun i : Fin 3 => (![node,code,param] i).relabel j) =
        ![node.relabel j,code.relabel j,param.relabel j] := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
    rw [hv] at hys
    change ∀ i, Nonempty (Derivation body Theta
      (graph3 (active U V i) (ys i) (node.relabel j) (code.relabel j) (param.relabel j))) at hys
    have hVj := renameInto hV j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,programRename,GuardedSourceSyntaxProof.numeralRename] at hVj
    have hnj := renameInto hn j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,programRename,GuardedSourceSyntaxProof.numeralRename] at hnj
    have hsourcej := renameInto hsource j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,programRename,GuardedSourceSyntaxProof.numeralRename] at hsourcej
    have htargetj := renameInto htarget j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,programRename,GuardedSourceSyntaxProof.numeralRename] at htargetj
    have hefj := renameInto hef j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,programRename,GuardedSourceSyntaxProof.numeralRename] at hefj
    have hegj := renameInto heg j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,programRename,GuardedSourceSyntaxProof.numeralRename] at hegj
    have hmj := renameInto hm j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,programRename,GuardedSourceSyntaxProof.numeralRename] at hmj
    have hc0j := renameInto hc0 j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,programRename,GuardedSourceSyntaxProof.numeralRename] at hc0j
    have hc1j := renameInto hc1 j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,programRename,GuardedSourceSyntaxProof.numeralRename] at hc1j
    have hc2j := renameInto hc2 j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,programRename,GuardedSourceSyntaxProof.numeralRename] at hc2j
    have hc3j := renameInto hc3 j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,programRename,GuardedSourceSyntaxProof.numeralRename] at hc3j
    have hj := renameInto h j Theta hj
    simp only [resultRename] at hj
    have hf := SupportProof.atFields body beta Theta U V
      (node.relabel j) (code.relabel j) (param.relabel j) (source.relabel j) (target.relabel j) (k.relabel j) (l.relabel j) (f.relabel j) (g.relabel j) (tau.relabel j) (upsilon.relabel j) (base.relabel j) (dest.relabel j) (ts.relabel j) (us.relabel j) (extras.relabel j) (otherExtras.relabel j) (ef.relabel j) (eg.relabel j) (move.relabel j) (h0.relabel j) (t0.relabel j) (h1.relabel j) (t1.relabel j) (h2.relabel j) (t2.relabel j) (h3.relabel j) (t3.relabel j)
      hVj hnj hsourcej htargetj hefj hegj hmj hc0j hc1j hc2j hc3j ys hys
    simp only [graph3Rename,GuardedSourceSyntaxProof.numeralRename]
    exact hf.mpr hj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralNumberedLayer.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralNumberedLayer.Proof
