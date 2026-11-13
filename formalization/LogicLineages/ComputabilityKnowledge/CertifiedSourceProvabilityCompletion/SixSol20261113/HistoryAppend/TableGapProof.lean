module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.TableLookupProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.TableGapProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport TableEquationsProof TableLookupProof

noncomputable def countCongruence {T : Sentence → Prop} {ctx : Nat} tag (s t right : Term ctx)
    (h : Derivation T (.equal s t)) :
    Derivation T (.equal (tableCall tag s right) (tableCall tag t right)) := by
  have d := Logic.unary (tableCall tag (.var 0) (liftTerm right)) s t h
  simpa only [substTable,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] using d

def template {ctx : Nat} (tag ltag htag : Nat) (base right : Term ctx) : Formula (ctx+1) :=
  .equal (HistoryLookup.lookupCall ltag (.var 0) (tableCall tag (.add (liftTerm base) (.var 0)) (liftTerm right)))
    (.succ (headCall htag (tableCall tag (liftTerm base) (liftTerm right))))

theorem templateAt {ctx : Nat} tag ltag htag (base right gap : Term ctx) :
    GorbowStandardInstances.instantiate (template tag ltag htag base right) gap =
      .equal (HistoryLookup.lookupCall ltag gap (tableCall tag (.add base gap) right))
        (.succ (headCall htag (tableCall tag base right))) := by
  simp only [GorbowStandardInstances.instantiate,template,substituteFormula,substLookup,substHead,substTable,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

/-- Symbolic course-of-values retrieval: index gap in table(base+gap)
returns SOME result(base), for arbitrary source terms base/gap/right. -/
theorem tableLookupGap {n ctx : Nat} (p : Program n) tag ltag htag
    (ht : (nodes p)[tag]? = some ⟨2,table⟩)
    (hl : (nodes p)[ltag]? = some ⟨2,HistoryLookup.lookup⟩)
    (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩) (base gap right : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (HistoryLookup.lookupCall ltag gap (tableCall tag (.add base gap) right))
        (.succ (headCall htag (tableCall tag base right))))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := template tag ltag htag base right
  obtain ⟨hz⟩ := tableLookupZero p tag ltag htag ht hl hh base right
  have hc0 := countCongruence tag (.add base .zero) base right (Derivation.arithmetic (A := T) (.addZero base))
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = template tag ltag htag base right from rfl,templateAt]
    exact Logic.trans _ _ _ (lookupCodeCongruence ltag .zero _ _ hc0) hz
  let B := liftTerm base
  let R := liftTerm right
  let x : Term (ctx+1) := .var 0
  let count := Term.add B x
  let previous := tableCall tag count R
  let entry := entryCall tag count previous R
  have hi : Hilbert.Local T (ctx+1) [phi]
      (.equal (HistoryLookup.lookupCall ltag x previous) (.succ (headCall htag (tableCall tag B R)))) := .hypothesis List.mem_cons_self
  obtain ⟨hstep⟩ := tableSuccessor p tag ht count R
  have hcount := countCongruence tag (.add B (.succ x)) (.succ count) R
    (Derivation.arithmetic (A := T) (.addSucc B x))
  have htab := Logic.trans _ _ _ hcount hstep
  obtain ⟨hlook⟩ := HistoryLookup.LookupProof.internalLookupSuccessorCons n p ltag (consTag tag)
    hl (consInstalled p tag ht) (ctx+1) x entry previous
  have hout := localTrans _ _ _ (.base (lookupCodeCongruence ltag (.succ x) _ _ htab))
    (localTrans _ _ _ (.base hlook) hi)
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simp only [phi,template,GorbowStandardInduction.successorInstance,substituteFormula,
      substLookup,substHead,substTable,substitute,successorLift,Fin.cases_zero]
    exact Hilbert.Local.finish (Hilbert.Local.discharge hout)
  have h := atTerm phi gap (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rw [show phi = template tag ltag htag base right from rfl,templateAt] at h
  exact ⟨h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.TableGapProof
