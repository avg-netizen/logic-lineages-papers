module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedDispatcherFuel.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.SuffixProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.StepSuffixProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.StepProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryKernel
open HistoryKernel.FieldsProof HistoryKernel.EntryProof HistoryKernel.TransitionEquationsProof HistoryKernel.OptionProof
open HistoryIteratorSuffix.StepSuffixProof (pairCongruence)

theorem activeStep {n ctx : Nat} (p : Program n) tag ptag ctag (v l a : Program 1) (x : Program 3)
 (ht : (nodes p)[tag]? = some ⟨3,kernel v l a (SaturatedAxiomLeaf.saturated x)⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index s t h line rest out : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (stepTransport tag ptag index s t h (HistoryLookup.consCall ctag line rest) out rest)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let ax := SaturatedAxiomLeaf.saturated x
 let E := Formula.equal (kernelCall tag (activeState ptag ctag h line rest) index s) (pairCall ptag (.succ out) rest)
 let G := [E,orderGuard s t]
 obtain ⟨hpair,hsel,heq,hdisp,hcons⟩ := kernelNodes p tag v l a ax ht
 obtain ⟨hparts⟩ := HistoryKernel.SuccessProof.successfulParts p tag ptag ctag v l a ax ht hp hc index s h line rest out
 obtain ⟨hmono⟩ := SaturatedDispatcherFuel.StatementChecks.internalMonotonicity v l a x n p (dispatcherTag tag v l a ax) hdisp ctx index s t h line
 obtain ⟨hopt⟩ := optionAccepted p tag v l a ax ht index t h line
 obtain ⟨hnew⟩ := HistoryKernel.NormalProof.kernelEquation p tag ptag ctag v l a ax ht hp hc index t h line rest
 obtain ⟨hcopy⟩ := HistoryDecoder.PairCongruenceProof.pairCopies p (outputPairTag tag v l a ax) ptag hpair hp (.succ out) rest
 have e : Hilbert.Local T ctx G E := .hypothesis List.mem_cons_self
 have ord : Hilbert.Local T ctx G (orderGuard s t) := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have parts := Hilbert.Local.mp (.base hparts) e
 have oldCheck := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) parts
 have oldShape := Hilbert.Local.mp (.base (.logical (.andRight _ _))) parts
 have newCheck := Hilbert.Local.mp (Hilbert.Local.mp (.base hmono) ord) oldCheck
 have optionShape := Hilbert.Local.mp (.base hopt) newCheck
 have successorShape := localUnary (.succ (.var 0)) _ _ oldShape
 have pairOption := HistoryKernel.SuffixProof.firstCongruence (outputPairTag tag v l a ax) _ _ rest optionShape
 have pairHistory := HistoryKernel.SuffixProof.firstCongruence (outputPairTag tag v l a ax) _ _ rest successorShape
 have result := localTrans _ _ _ (.base hnew) (localTrans _ _ _ pairOption (localTrans _ _ _ pairHistory (.base hcopy)))
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge result))⟩

theorem nilStep {n ctx : Nat} (p : Program n) tag ptag (v l a : Program 1) (x : Program 3)
 (ht : (nodes p)[tag]? = some ⟨3,kernel v l a (SaturatedAxiomLeaf.saturated x)⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (index s t h out rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (stepTransport tag ptag index s t h .zero out rest)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let E := Formula.equal (kernelCall tag (pairCall ptag (.succ h) .zero) index s) (pairCall ptag (.succ out) rest)
 obtain ⟨hs⟩ := HistoryIteratorSuffix.StateEquationsProof.kernelNil p tag ptag v l a (SaturatedAxiomLeaf.saturated x) ht hp (.succ h) index s
 obtain ⟨ht'⟩ := HistoryIteratorSuffix.StateEquationsProof.kernelNil p tag ptag v l a (SaturatedAxiomLeaf.saturated x) ht hp (.succ h) index t
 have e : Hilbert.Local T ctx [E,orderGuard s t] E := .hypothesis List.mem_cons_self
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
  (localTrans _ _ _ (.base ht') (localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hs)) e))))⟩

theorem consStep {n ctx : Nat} (p : Program n) tag ptag ctag (v l a : Program 1) (x : Program 3)
 (ht : (nodes p)[tag]? = some ⟨3,kernel v l a (SaturatedAxiomLeaf.saturated x)⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index s t h line lines out rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (stepTransport tag ptag index s t h (HistoryLookup.consCall ctag line lines) out rest)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let ax := SaturatedAxiomLeaf.saturated x
 let E := Formula.equal (kernelCall tag (activeState ptag ctag h line lines) index s) (pairCall ptag (.succ out) rest)
 let G := [E,orderGuard s t]
 obtain ⟨he⟩ := HistoryKernel.NormalProof.kernelEquation p tag ptag ctag v l a ax ht hp hc index s h line lines
 obtain ⟨hpair,_,_,_,_⟩ := kernelNodes p tag v l a ax ht
 obtain ⟨hcopy⟩ := HistoryDecoder.PairCongruenceProof.pairCopies p (outputPairTag tag v l a ax) ptag hpair hp
  (optionValue tag v l a ax index s h line) lines
 have en := Logic.trans _ _ _ he hcopy
 obtain ⟨hi⟩ := HistoryCancellation.InjectivityProof.pairInjective n p ptag hp ctx
  (optionValue tag v l a ax index s h line) lines (.succ out) rest
 have hh : Hilbert.Local T ctx G E := .hypothesis List.mem_cons_self
 have ord : Hilbert.Local T ctx G (orderGuard s t) := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have ep := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ en)) hh
 have both := Hilbert.Local.mp (.base hi) ep
 have er : Hilbert.Local T ctx G (.equal lines rest) := .mp (.base (.logical (.andRight _ _))) both
 have eo := pairCongruence ptag (.succ out) lines (.succ out) rest (.base (.logical (.reflexive _))) er
 have old := localTrans _ _ _ hh (HistoryOrder.StepProof.localSym _ _ eo)
 obtain ⟨hs⟩ := activeStep p tag ptag ctag v l a x ht hp hc index s t h line lines out
 have next := Hilbert.Local.mp (Hilbert.Local.mp (.base hs) ord) old
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (localTrans _ _ _ next eo)))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.StepProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.StepProof
