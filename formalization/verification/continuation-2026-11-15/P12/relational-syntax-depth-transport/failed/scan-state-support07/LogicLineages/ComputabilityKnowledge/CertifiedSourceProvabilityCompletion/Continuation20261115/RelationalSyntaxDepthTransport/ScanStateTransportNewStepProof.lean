module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportNewStepProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph
open LiteralSyntaxScan.StateRecursionProof LiteralSyntaxScan.Fusion
open ScanStateTransportSupportProof ScanStateTransportBoundProof

def claim {ctx : Nat} (itag len ptag q l r ctag stag : Nat)
 (token raw ot nt result oldNext : Term ctx) : Formula ctx :=
 .imp (allStacks itag len ptag q l r raw)
  (.imp (.equal (LiteralSyntaxStep.stepCall stag (.succ ot) token) (.succ oldNext))
   (.imp (.equal (scanState itag len ptag r (HistoryLookup.consCall ctag token raw) (.succ ot)) (.succ result))
    (ScanStateTransportTargets.witnesses itag len ptag q l r (HistoryLookup.consCall ctag token raw) nt result)))
theorem substClaim {m n : Nat} (s : Fin m → Term n) itag len ptag q l r ctag stag
 (token raw ot nt result oldNext : Term m) :
 substituteFormula s (claim itag len ptag q l r ctag stag token raw ot nt result oldNext) =
 claim itag len ptag q l r ctag stag (substitute s token) (substitute s raw) (substitute s ot)
  (substitute s nt) (substitute s result) (substitute s oldNext) := by
 simp only [claim,substituteFormula,substAllStacks,substScanState,substWitnesses,
  HistoryLookup.DropEquationsProof.substCons,LiteralSyntaxStep.stepCall,SixSol20261112.Fuel.Logic.substCall,
  List.Vector.map_cons,List.Vector.map_nil,substitute]
/-- Eliminate the new intermediate task-stack supplied by exact StepTransport;
it is never an external run/step supplier. -/
theorem eliminateNew {n ctx : Nat} (p : Program n) (itag len ptag q l r ctag stag : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,LiteralSyntaxScan.iterator⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (token raw ot nt result oldNext : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (StepTransportTargets.witnesses stag len q l r nt token oldNext)
   (claim itag len ptag q l r ctag stag token raw ot nt result oldNext))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := StepTransportTargets.witnessBody stag len q l r (liftTerm nt) (liftTerm token) (liftTerm oldNext) (.var (0 : Fin (ctx+1)))
 let I := allStacks itag len ptag q l r (liftTerm raw)
 let O := Formula.equal (LiteralSyntaxStep.stepCall stag (.succ (liftTerm ot)) (liftTerm token)) (.succ (liftTerm oldNext))
 let S := Formula.equal (scanState itag len ptag r (HistoryLookup.consCall ctag (liftTerm token) (liftTerm raw)) (.succ (liftTerm ot))) (.succ (liftTerm result))
 let G := [S,O,I,H]
 have hw : Hilbert.Local T (ctx+1) G H := .hypothesis (by simp [G])
 have hn := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hw
 have hrel := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hw
 have hih : Hilbert.Local T (ctx+1) G I := .hypothesis (by simp [G])
 have ho : Hilbert.Local T (ctx+1) G O := .hypothesis (by simp [G])
 have hold : Hilbert.Local T (ctx+1) G S := .hypothesis (by simp [G])
 obtain ⟨hout⟩ := ScanStateTransportConsProof.positiveAt p G itag len ptag q l r ctag stag hi hlen hp hc hs
  (liftTerm token) (liftTerm raw) (liftTerm ot) (liftTerm nt) (liftTerm result) (liftTerm oldNext) (.var 0)
  hih hrel ho hn hold
 have hb : Derivation T (.imp H (GorbowPACore.weaken (claim itag len ptag q l r ctag stag token raw ot nt result oldNext))) := by
  rw [GorbowPACore.weaken,substClaim]
  simpa only [G,I,O,S,claim,liftTerm,renameTerm] using hout.discharge.discharge.discharge.discharge.finish
 exact HBQuantifier.existentialElimination T H (claim itag len ptag q l r ctag stag token raw ot nt result oldNext) ⟨hb⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportNewStepProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportNewStepProof
