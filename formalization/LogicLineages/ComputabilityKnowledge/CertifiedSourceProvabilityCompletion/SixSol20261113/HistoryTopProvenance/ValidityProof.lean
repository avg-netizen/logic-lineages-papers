module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.OccurrenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.ValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryKernel.TransitionEquationsProof

theorem dispatcherNonzero {n ctx : Nat} (p : Program n) itag (v l a : Program 1) (x : Program 3)
 (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
 (index fuel history line : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (.imp (.equal (HistoryDispatcher.dispatcherCall (dispatcherTag (kernelTag itag) v l a x)
       index fuel history line) (.succ .zero))
     (.neg (.equal (call (validityTag itag v l a x) (line ::ᵥ nil)) .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let dt := dispatcherTag (kernelTag itag) v l a x
 let g := HistoryTopProvenance.dispatcherArguments v l a x
 let args := HistoryDispatcher.IndependenceProof.args index fuel history line
 let vt := dt + argumentTag HistoryCodec.select g 0
 let zt := dt + argumentTag HistoryCodec.select g 1
 let rt := dt + argumentTag HistoryCodec.select g 2
 let C := call dt args
 let V := call (validityTag itag v l a x) (line ::ᵥ nil)
 let E := Formula.equal C (.succ .zero)
 let Z := Formula.equal V .zero
 have hd := OccurrenceProof.dispatcherInstalled p itag v l a x hi
 have hv := Equations.argumentChild p dt HistoryCodec.select g hd 0
 have hz := Equations.argumentChild p dt HistoryCodec.select g hd 1
 have hselect := Equations.functionChild p dt HistoryCodec.select g hd
 obtain ⟨hvalue⟩ := HistoryAppend.ValueEquationsProof.unaryValues p vt v
   (fun _ : Fin 1 => HistoryDispatcher.lineCode) hv args line
   (Equations.projection p _ (3 : Fin 4)
     (Equations.argumentChild p vt v (fun _ : Fin 1 => HistoryDispatcher.lineCode) hv 0) args)
 obtain ⟨hzero⟩ := HistoryAppend.TableEquationsProof.zeroEquation p zt hz args
 obtain ⟨hcomp⟩ := GorbowPRSymbolicEquations.Proof.compositionEquation n p dt 4 3 HistoryCodec.select g hd ctx args
 have hcomp' : Derivation T (.equal C
   (call (dt+1) (call vt args ::ᵥ call zt args ::ᵥ call rt args ::ᵥ nil))) := hcomp
 obtain ⟨hs⟩ := HistoryCodec.PairProof.selectZero p (dt+1) hselect (call zt args) (call rt args)
 have he : Hilbert.Local T ctx [.neg (.neg Z),E] E := .hypothesis (by simp)
 have hvzero : Hilbert.Local T ctx [.neg (.neg Z),E] Z :=
   .mp (.base (Hilbert.doubleNegation Z)) (.hypothesis List.mem_cons_self)
 have htzero := localTrans _ _ _ (.base hvalue) hvzero
 have hchange := HistoryDecoder.SelectGraphProof.testCongruence (dt+1)
   (call vt args) .zero (call zt args) (call rt args) htzero
 have hc0 := localTrans _ _ _ (.base hcomp')
   (localTrans _ _ _ hchange (localTrans _ _ _ (.base hs) (.base hzero)))
 have bad := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ he) hc0
 have hn : Hilbert.Local T ctx [E] (.neg Z) :=
   Hilbert.Local.classical (.neg Z)
     (Hilbert.Local.explosion (.neg Z) bad (.base (.arithmetic (.succNotZero .zero))))
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hn)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.ValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.ValidityProof
