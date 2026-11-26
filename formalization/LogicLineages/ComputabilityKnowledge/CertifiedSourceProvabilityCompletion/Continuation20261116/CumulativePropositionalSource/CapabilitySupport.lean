module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.InstallationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CapabilitySupport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem inSource (f : Formula 1) (lhs rhs : Term 1) (pF pR old a : Program 1) (baseX : Program 3)
 {ctx : Nat} (phi : Formula ctx)
 (h : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory (root f lhs rhs pF pR old a baseX)) phi)) :
 Nonempty (Derivation (S pF pR (verifier f lhs rhs old a baseX)) phi) :=
 GorbowTheoryProofProof.monotonicity _ _ (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx phi h
theorem retentionInternal {n k ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x)
 (index fuel context formula code : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (LiteralCheckerAcceptance.coreCall I.previous.current.coreTag index fuel context formula code) (.succ .zero))
   (.equal (LiteralCheckerAcceptance.coreCall I.currentK.coreTag index fuel context formula code) (.succ .zero)))) := by
 have hd := SixSol20261112.Fuel.Equations.argumentChild p I.previous.current.qtag HistoryLookup.reference
  (fun _ : Fin 1 => HistoryLookup.drop) I.previous.current.h_qtag 0
 exact UniformClosedPropositionalCoreRetention.StatementChecks.exactCoreRetention n p
  LiteralSyntaxValidator.lineValidator (previousLogical f lhs rhs old) (arithmetic a) x
  I.previous.current.coreTag I.currentK.coreTag I.previous.current.ptag I.previous.current.ctag I.previous.current.rtag
  (HistoryLookup.LookupProof.dropTag I.previous.current.qtag)
  I.previous.current.h_core I.currentK.h_coreTag I.previous.current.h_ptag I.previous.current.h_ctag I.previous.current.h_rtag hd
  ctx index fuel context formula code
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CapabilitySupport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CapabilitySupport
