module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.GraphCongruenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OperatorCongruenceProof
open InternalControlGraph
open GraphCongruenceProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
attribute [local irreducible] ProgramGraphEquivalent programGraph

theorem postcompose {m n : Nat} {p q : Program n}
    (hp : ProgramGraphEquivalent p q) (gs : Fin n → Program m) :
    ProgramGraphEquivalent (.composition p gs) (.composition q gs) :=
  compositionCongruence hp (fun i => equivalentRefl (gs i))

theorem precompose {m n : Nat} (p : Program n)
    {gs hs : Fin n → Program m}
    (hg : ∀ i, ProgramGraphEquivalent (gs i) (hs i)) :
    ProgramGraphEquivalent (.composition p gs) (.composition p hs) :=
  compositionCongruence (equivalentRefl p) hg

theorem branchCongruence {n : Nat} {c d z w p q : Program n}
    (hc : ProgramGraphEquivalent c d) (hz : ProgramGraphEquivalent z w)
    (hp : ProgramGraphEquivalent p q) :
    ProgramGraphEquivalent (InternalAcceptance.branch c z p)
      (InternalAcceptance.branch d w q) := by
  unfold InternalAcceptance.branch
  apply precompose
  intro i
  exact Fin.cases hc (fun i => Fin.cases hz (fun i => Fin.cases hp Fin.elim0 i) i) i

theorem normalizeCongruence {n : Nat} {p q : Program n}
    (hp : ProgramGraphEquivalent p q) :
    ProgramGraphEquivalent (GorbowVerifierNormalization.normalize p)
      (GorbowVerifierNormalization.normalize q) := by
  unfold GorbowVerifierNormalization.normalize
  exact precompose _ (fun _ => hp)

theorem conjunctionCongruence {n : Nat} {p q r s : Program n}
    (hp : ProgramGraphEquivalent p q) (hr : ProgramGraphEquivalent r s) :
    ProgramGraphEquivalent (InternalAcceptance.conjunction p r)
      (InternalAcceptance.conjunction q s) := by
  unfold InternalAcceptance.conjunction
  exact branchCongruence (normalizeCongruence hp) (equivalentRefl _)
    (normalizeCongruence hr)

theorem sameCongruence {n : Nat} {p q r s : Program n}
    (hp : ProgramGraphEquivalent p q) (hr : ProgramGraphEquivalent r s) :
    ProgramGraphEquivalent (InternalApplicationStepPeel.same p r)
      (InternalApplicationStepPeel.same q s) := by
  unfold InternalApplicationStepPeel.same
  apply precompose
  intro i
  exact Fin.cases hp (fun i => Fin.cases hr Fin.elim0 i) i

theorem tableBaseCongruence {k : Nat} {p q : Program k}
    (hp : ProgramGraphEquivalent p q) :
    ProgramGraphEquivalent (InternalRawListRecursion.tableBase p)
      (InternalRawListRecursion.tableBase q) := by
  unfold InternalRawListRecursion.tableBase
  apply precompose
  intro i
  exact Fin.cases hp (fun i => Fin.cases (equivalentRefl _) Fin.elim0 i) i

theorem nextValueCongruence {k : Nat} {p q : Program (k + 2)}
    (hp : ProgramGraphEquivalent p q) :
    ProgramGraphEquivalent (InternalRawListRecursion.nextValue p)
      (InternalRawListRecursion.nextValue q) := by
  unfold InternalRawListRecursion.nextValue
  exact postcompose hp _

theorem tableStepCongruence {k : Nat} {p q : Program (k + 2)}
    (hp : ProgramGraphEquivalent p q) :
    ProgramGraphEquivalent (InternalRawListRecursion.tableStep p)
      (InternalRawListRecursion.tableStep q) := by
  unfold InternalRawListRecursion.tableStep
  apply precompose
  intro i
  exact Fin.cases (nextValueCongruence hp)
    (fun i => Fin.cases (equivalentRefl _) Fin.elim0 i) i

theorem listRecCongruence {k : Nat} {p q : Program k} {g h : Program (k + 2)}
    (hp : ProgramGraphEquivalent p q) (hg : ProgramGraphEquivalent g h) :
    ProgramGraphEquivalent (InternalRawListRecursion.listRec p g)
      (InternalRawListRecursion.listRec q h) := by
  unfold InternalRawListRecursion.listRec InternalRawListRecursion.table
  exact precompose _ (fun _ =>
    recursionCongruence (tableBaseCongruence hp) (tableStepCongruence hg))

theorem repeatCongruence {p q : Program 1} (hp : ProgramGraphEquivalent p q) :
    ProgramGraphEquivalent (InternalRawListRepeat.repeatProgram p)
      (InternalRawListRepeat.repeatProgram q) := by
  unfold InternalRawListRepeat.repeatProgram InternalRawListRepeat.repeatStep
  exact listRecCongruence (equivalentRefl _) (postcompose hp _)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OperatorCongruenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OperatorCongruenceProof
