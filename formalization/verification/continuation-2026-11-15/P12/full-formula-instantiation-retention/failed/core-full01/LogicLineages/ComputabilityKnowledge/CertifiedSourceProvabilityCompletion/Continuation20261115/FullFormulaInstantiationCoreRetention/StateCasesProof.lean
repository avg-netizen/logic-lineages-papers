module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCoreRetention.KernelProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCoreRetention.State.CasesProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open RawUniversalStateRetention RawUniversalStateRetention.TransportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryKernel
open HistoryIteratorSuffix HistoryIteratorSuffix.WitnessProof HistoryIteratorSuffix.StepSuffixProof
open RawUniversalStateRetention.TransportProof HistoryKernel.TransitionEquationsProof

theorem nilStep {n ctx : Nat} (template : Formula 1) (p : Program n) (ot nt ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
 (ho : (nodes p)[ot]? = some ⟨3,kernel v l a x⟩)
 (hn : (nodes p)[nt]? = some ⟨3,kernel v (FullFormulaInstantiation.logicalLeaf template l) a x⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel h out rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (preserves ot nt ptag (pairCall ptag (.succ h) .zero) index fuel out rest)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := Formula.equal (kernelCall ot (pairCall ptag (.succ h) .zero) index fuel) (pairCall ptag (.succ out) rest)
 obtain ⟨hz⟩ := HistoryIteratorSuffix.StateEquationsProof.kernelNil p ot ptag v l a x ho hp (.succ h) index fuel
 obtain ⟨hnil⟩ := HistoryIteratorSuffix.StateEquationsProof.kernelNil p nt ptag v (FullFormulaInstantiation.logicalLeaf template l) a x hn hp (.succ h) index fuel
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ (.base hnil)
  (localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hz)) hh)))⟩

theorem consStep {n ctx : Nat} (template : Formula 1) (p : Program n) (ot nt ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
 (ho : (nodes p)[ot]? = some ⟨3,kernel v l a x⟩)
 (hn : (nodes p)[nt]? = some ⟨3,kernel v (FullFormulaInstantiation.logicalLeaf template l) a x⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (index fuel h line lines out rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (preserves ot nt ptag (activeState ptag ctag h line lines) index fuel out rest)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := Formula.equal (kernelCall ot (activeState ptag ctag h line lines) index fuel) (pairCall ptag (.succ out) rest)
 obtain ⟨he⟩ := HistoryKernel.NormalProof.kernelEquation p ot ptag ctag v l a x ho hp hc index fuel h line lines
 obtain ⟨hop,_,_,_,_⟩ := HistoryKernel.OptionProof.kernelNodes p ot v l a x ho
 obtain ⟨hcopy⟩ := HistoryDecoder.PairCongruenceProof.pairCopies p (outputPairTag ot v l a x) ptag hop hp
  (optionValue ot v l a x index fuel h line) lines
 have en := Logic.trans _ _ _ he hcopy
 obtain ⟨hi⟩ := HistoryCancellation.InjectivityProof.pairInjective n p ptag hp ctx
  (optionValue ot v l a x index fuel h line) lines (.succ out) rest
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have both := Hilbert.Local.mp (.base hi) (localTrans _ _ _ (.base (Support.equalitySymmetry _ _ en)) hh)
 have er : Hilbert.Local T ctx [H] (.equal lines rest) := .mp (.base (.logical (.andRight _ _))) both
 have eo := pairCongruence ptag (.succ out) lines (.succ out) rest (.base (.logical (.reflexive _))) er
 have old := localTrans _ _ _ hh (HistoryOrder.StepProof.localSym _ _ eo)
 obtain ⟨hs⟩ := Kernel.Proof.internalActiveStep template n p v l a x ot nt ptag ctag ho hn hp hc ctx index fuel h line lines out
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ (.mp (.base hs) old) eo))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCoreRetention.State.CasesProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCoreRetention.State.CasesProof
