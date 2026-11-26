module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ResultStructuralFields.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ResultStructuralFields.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ResultStructuralFields.SupportProof

def result {alpha : Type} (ef eg rf rg move h0 : OTerm alpha) : Formula alpha :=
  (eqn move (numeral 1) ⊓ eqn rg rf) ⊔ (eqn ef eg ⊓ eqn h0 (numeral 1))
theorem resultRename {alpha beta : Type} (ef eg rf rg move h0 : OTerm alpha) (j : alpha → beta) :
    (result ef eg rf rg move h0).relabel j =
      result (ef.relabel j) (eg.relabel j) (rf.relabel j) (rg.relabel j) (move.relabel j) (h0.relabel j) := by
  simp only [result,StructuralExchangeFields.InternalProof.andRename,
    StructuralExchangeFields.InternalProof.orRename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename]

theorem internalOrdinary : Targets.InternalOrdinary := by
  intro body alpha Delta U V node code param source target f g base dest ef eg rf rg move h0 t0
    hV hn hsource htarget hef heg hrf hrg hm hc
  constructor
  · intro h
    change Nonempty (Derivation body Delta (result ef eg rf rg move h0))
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
    simp only [graph3Rename,graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hVj
    have hnj := renameInto hn j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hnj
    have hsourcej := renameInto hsource j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hsourcej
    have htargetj := renameInto htarget j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at htargetj
    have hefj := renameInto hef j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hefj
    have hegj := renameInto heg j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hegj
    have hrfj := renameInto hrf j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hrfj
    have hrgj := renameInto hrg j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hrgj
    have hmj := renameInto hm j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
    have hcj := renameInto hc j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hcj
    have hj := renameInto h j Theta hj
    simp only [graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hj
    have hf := SupportProof.atFields body beta Theta U V
      (node.relabel j) (code.relabel j) (param.relabel j) (source.relabel j) (target.relabel j) (f.relabel j) (g.relabel j) (base.relabel j) (dest.relabel j) (ef.relabel j) (eg.relabel j) (rf.relabel j) (rg.relabel j) (move.relabel j) (h0.relabel j) (t0.relabel j)
      hVj hnj hsourcej htargetj hefj hegj hrfj hrgj hmj hcj ys hys
    simp only [resultRename]
    exact hf.mp hj
  · intro h
    change Nonempty (Derivation body Delta (result ef eg rf rg move h0)) at h
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
    simp only [graph3Rename,graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hVj
    have hnj := renameInto hn j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hnj
    have hsourcej := renameInto hsource j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hsourcej
    have htargetj := renameInto htarget j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at htargetj
    have hefj := renameInto hef j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hefj
    have hegj := renameInto heg j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hegj
    have hrfj := renameInto hrf j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hrfj
    have hrgj := renameInto hrg j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hrgj
    have hmj := renameInto hm j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
    have hcj := renameInto hc j Theta hj
    simp only [graph3Rename,graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hcj
    have hj := renameInto h j Theta hj
    simp only [resultRename] at hj
    have hf := SupportProof.atFields body beta Theta U V
      (node.relabel j) (code.relabel j) (param.relabel j) (source.relabel j) (target.relabel j) (f.relabel j) (g.relabel j) (base.relabel j) (dest.relabel j) (ef.relabel j) (eg.relabel j) (rf.relabel j) (rg.relabel j) (move.relabel j) (h0.relabel j) (t0.relabel j)
      hVj hnj hsourcej htargetj hefj hegj hrfj hrgj hmj hcj ys hys
    simp only [graph3Rename,GuardedSourceSyntaxProof.numeralRename]
    exact hf.mpr hj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ResultStructuralFields.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ResultStructuralFields.InternalProof
