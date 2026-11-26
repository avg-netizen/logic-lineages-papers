module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumericSearch.RecurrenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumericSearch.WitnessProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open GorbowSubstitution GorbowFormulaSubstitution

def premise {ctx : Nat} (q : Nat) (i line : Term ctx) : Formula ctx :=
 .equal (testCall q i line) (.succ .zero)
def conclusion {ctx : Nat} (s : Nat) (i j line : Term ctx) : Formula ctx :=
 .equal (searchCall s (.succ (.add i j)) line) (.succ .zero)
def template {ctx : Nat} (q s : Nat) (i line : Term ctx) : Formula (ctx+1) :=
 .imp (premise q (liftTerm i) (liftTerm line))
  (conclusion s (liftTerm i) (.var 0) (liftTerm line))
theorem templateAt {ctx : Nat} q s (i j line : Term ctx) :
 GorbowStandardInstances.instantiate (template q s i line) j =
 .imp (premise q i line) (conclusion s i j line) := by
 simp only [GorbowStandardInstances.instantiate,template,premise,conclusion,substituteFormula,
  searchCall,testCall,Logic.substCall,
  List.Vector.map_cons,List.Vector.map_nil,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

noncomputable def countCongruence {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (tag : Nat) (a b line : Term ctx)
 (h : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a b)) :
 Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
 (.equal (searchCall tag a line) (searchCall tag b line)) :=
 callCongruence (T := GorbowPRNumeralCalculation.Theory p) (G := G) tag
  (a ::ᵥ line ::ᵥ nil) (b ::ᵥ line ::ᵥ nil) (fun k => by
   cases k using Fin.cases with
   | zero => exact .base h
   | succ k => cases k using Fin.cases with
     | zero => exact .base (.logical (.reflexive line))
     | succ k => exact Fin.elim0 k)

theorem internalWitness : Targets.InternalWitness := by
 intro n p test I ctx i j line
 let T := GorbowPRNumeralCalculation.Theory p
 let phi := template I.testTag I.searchTag i line
 let H := premise I.testTag i line
 obtain ⟨hnext⟩ := RecurrenceProof.witnessNext p test I i line
 have hz : Derivation T (.equal (.succ (.add i .zero)) (.succ i)) :=
  Hilbert.Local.finish (localUnary (.succ (.var 0)) _ _ (.base (.arithmetic (.addZero i))))
 have hc := countCongruence p [H] I.searchTag _ _ line hz
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have hout := localTrans _ _ _ hc (.mp (.base hnext) hh)
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
  simpa only [phi,templateAt,H,premise,conclusion] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
 let i' := liftTerm i
 let line' := liftTerm line
 let k : Term (ctx+1) := .var 0
 let H' := premise I.testTag i' line'
 let G := [H',phi]
 have hih : Hilbert.Local T (ctx+1) G phi := .hypothesis (by simp [G])
 have hh' : Hilbert.Local T (ctx+1) G H' := .hypothesis List.mem_cons_self
 have hprev : Hilbert.Local T (ctx+1) G (conclusion I.searchTag i' k line') := .mp hih hh'
 obtain ⟨hp⟩ := RecurrenceProof.internalPersistence n p test I (ctx+1) (.succ (.add i' k)) line'
 have hsucc := Hilbert.Local.mp (.base hp) hprev
 have he : Derivation T (.equal (.succ (.add i' (.succ k))) (.succ (.succ (.add i' k)))) :=
  Hilbert.Local.finish (localUnary (.succ (.var 0)) _ _ (.base (.arithmetic (.addSucc i' k))))
 have hcg := countCongruence p G I.searchTag _ _ line' he
 have hresult := localTrans _ _ _ hcg hsucc
 have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simpa only [phi,template,premise,conclusion,G,H',GorbowStandardInduction.successorInstance,
   substituteFormula,searchCall,testCall,
   Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,successorLift,Fin.cases_zero,i',line',k]
   using Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hresult))
 have h := atTerm phi j (HistoryCodec.ArithmeticSupport.induction phi hb hs)
 exact ⟨by simpa only [phi,templateAt,premise,conclusion,T] using h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumericSearch.WitnessProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumericSearch.WitnessProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumericSearch.WitnessProof.internalWitness
