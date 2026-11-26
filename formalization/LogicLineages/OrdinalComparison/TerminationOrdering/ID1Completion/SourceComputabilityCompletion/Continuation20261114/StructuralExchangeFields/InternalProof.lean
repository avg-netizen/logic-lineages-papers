module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.AtFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionTotalityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
public import Mathlib.Tactic.FinCases
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SupportProof

def result {alpha : Type} (sigma tau q a r b h0 h3 : OTerm alpha) : Formula alpha :=
  eqn sigma tau ⊓ ((eqn a b ⊓ eqn h0 (numeral 1)) ⊔ (eqn q r ⊓ eqn h3 (numeral 1)))

theorem andRename {alpha beta : Type} (p q : Formula alpha) (j : alpha → beta) :
    (p ⊓ q).relabel j = p.relabel j ⊓ q.relabel j := rfl

theorem orRename {alpha beta : Type} (p q : Formula alpha) (j : alpha → beta) :
    (p ⊔ q).relabel j = p.relabel j ⊔ q.relabel j := rfl

theorem resultRename {alpha beta : Type} (sigma tau q a r b h0 h3 : OTerm alpha) (j : alpha → beta) :
    (result sigma tau q a r b h0 h3).relabel j =
      result (sigma.relabel j) (tau.relabel j) (q.relabel j) (a.relabel j)
        (r.relabel j) (b.relabel j) (h0.relabel j) (h3.relabel j) := by
  simp only [result,andRename,orRename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename]

theorem internalApplication : Targets.InternalApplication := by
  intro body alpha Delta U V cons node code param source target sigma tau q a r b h0 t0 h1 t1 h2 t2 h3 t3
    hV hn hsource htarget hc0 hc1 hc2 hc3
  constructor
  · intro h
    change Nonempty (Derivation body Delta (result sigma tau q a r b h0 h3))
    apply InternalGraphCompositionTotalityProof.supplyOutputs body 3 19
      (fun i => OrdinaryArithmetic.graphFormula (active U V i))
      (fun i => (InternalRecursionClosureProof.actualOriginalPrograms body 3 (active U V i)).1)
      alpha Delta ![node,code,param] _
    intro beta j Theta ys hj hys
    have hv : (fun i : Fin 3 => (![node,code,param] i).relabel j) =
        ![node.relabel j,code.relabel j,param.relabel j] := by
      funext i
      fin_cases i <;> rfl
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
    have hc0j := renameInto hc0 j Theta hj
    simp only [graph3Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hc0j
    have hc1j := renameInto hc1 j Theta hj
    simp only [graph3Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hc1j
    have hc2j := renameInto hc2 j Theta hj
    simp only [graph3Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hc2j
    have hc3j := renameInto hc3 j Theta hj
    simp only [graph3Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hc3j
    have hj := renameInto h j Theta hj
    simp only [graph3Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hj
    have hf := AtFieldsProof.atFields body beta Theta U V cons
      (node.relabel j) (code.relabel j) (param.relabel j) (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (h0.relabel j) (t0.relabel j) (h1.relabel j) (t1.relabel j) (h2.relabel j) (t2.relabel j) (h3.relabel j) (t3.relabel j)
      hVj hnj hsourcej htargetj hc0j hc1j hc2j hc3j ys hys
    simp only [resultRename]
    exact hf.mp hj
  · intro h
    change Nonempty (Derivation body Delta (graph3 (layer U V) (numeral 2) node code param))
    change Nonempty (Derivation body Delta (result sigma tau q a r b h0 h3)) at h
    apply InternalGraphCompositionTotalityProof.supplyOutputs body 3 19
      (fun i => OrdinaryArithmetic.graphFormula (active U V i))
      (fun i => (InternalRecursionClosureProof.actualOriginalPrograms body 3 (active U V i)).1)
      alpha Delta ![node,code,param] _
    intro beta j Theta ys hj hys
    have hv : (fun i : Fin 3 => (![node,code,param] i).relabel j) =
        ![node.relabel j,code.relabel j,param.relabel j] := by
      funext i
      fin_cases i <;> rfl
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
    have hc0j := renameInto hc0 j Theta hj
    simp only [graph3Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hc0j
    have hc1j := renameInto hc1 j Theta hj
    simp only [graph3Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hc1j
    have hc2j := renameInto hc2 j Theta hj
    simp only [graph3Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hc2j
    have hc3j := renameInto hc3 j Theta hj
    simp only [graph3Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hc3j
    have hj := renameInto h j Theta hj
    simp only [resultRename] at hj
    have hf := AtFieldsProof.atFields body beta Theta U V cons
      (node.relabel j) (code.relabel j) (param.relabel j) (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (h0.relabel j) (t0.relabel j) (h1.relabel j) (t1.relabel j) (h2.relabel j) (t2.relabel j) (h3.relabel j) (t3.relabel j)
      hVj hnj hsourcej htargetj hc0j hc1j hc2j hc3j ys hys
    simp only [graph3Rename,GuardedSourceSyntaxProof.numeralRename]
    exact hf.mpr hj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.InternalProof
