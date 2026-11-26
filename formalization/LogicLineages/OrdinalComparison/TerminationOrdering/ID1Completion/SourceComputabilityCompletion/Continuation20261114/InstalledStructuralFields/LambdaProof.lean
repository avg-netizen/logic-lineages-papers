module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledStructuralFields.LambdaSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledStructuralFields.LambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open StructuralExchangeFields.SupportProof

def result {alpha : Type} (sigma tau h0 : OTerm alpha) : Formula alpha := eqn sigma tau ⊓ eqn h0 (numeral 1)
theorem resultRename {alpha beta : Type} (sigma tau h0 : OTerm alpha) (j : alpha → beta) :
    (result sigma tau h0).relabel j = result (sigma.relabel j) (tau.relabel j) (h0.relabel j) := by
  simp only [result,StructuralExchangeFields.InternalProof.andRename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename]

theorem internalLambda : Targets.InternalLambda := by
  intro U V body alpha Delta node code param source target sigma tau q r h0 t0 hV hn hsource htarget hc
  constructor
  · intro h
    change Nonempty (Derivation body Delta (result sigma tau h0))
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
    simp only [graph3Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hVj
    have hnj := renameInto hn j Theta hj
    simp only [graph3Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hnj
    have hsourcej := renameInto hsource j Theta hj
    simp only [graph3Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsourcej
    have htargetj := renameInto htarget j Theta hj
    simp only [graph3Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at htargetj
    have hcj := renameInto hc j Theta hj
    simp only [graph3Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hcj
    have hj := renameInto h j Theta hj
    simp only [graph3Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hj
    have hf := LambdaSupportProof.atFields U V body beta Theta
      (node.relabel j) (code.relabel j) (param.relabel j) (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (r.relabel j) (h0.relabel j) (t0.relabel j)
      hVj hnj hsourcej htargetj hcj ys hys
    simp only [resultRename]
    exact hf.mp hj
  · intro h
    change Nonempty (Derivation body Delta (graph3 (StructuralExchangeFields.layer U V) (numeral 2) node code param))
    change Nonempty (Derivation body Delta (result sigma tau h0)) at h
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
    simp only [graph3Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hVj
    have hnj := renameInto hn j Theta hj
    simp only [graph3Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hnj
    have hsourcej := renameInto hsource j Theta hj
    simp only [graph3Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsourcej
    have htargetj := renameInto htarget j Theta hj
    simp only [graph3Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at htargetj
    have hcj := renameInto hc j Theta hj
    simp only [graph3Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hcj
    have hj := renameInto h j Theta hj
    simp only [resultRename] at hj
    have hf := LambdaSupportProof.atFields U V body beta Theta
      (node.relabel j) (code.relabel j) (param.relabel j) (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (r.relabel j) (h0.relabel j) (t0.relabel j)
      hVj hnj hsourcej htargetj hcj ys hys
    simp only [graph3Rename,GuardedSourceSyntaxProof.numeralRename]
    exact hf.mpr hj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledStructuralFields.LambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledStructuralFields.LambdaProof
