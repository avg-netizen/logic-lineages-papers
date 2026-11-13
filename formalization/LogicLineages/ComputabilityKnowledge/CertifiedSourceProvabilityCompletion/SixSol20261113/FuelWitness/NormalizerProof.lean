module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.NormalizerEquationsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.NormalizerProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPRDefiningEquations GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport NormalizerEquationsProof

def weaken {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} {phi q : Formula ctx} :
 Hilbert.Local T ctx G phi → Hilbert.Local T ctx (q :: G) phi
 | .base d => .base d
 | .hypothesis h => .hypothesis (List.mem_cons_of_mem _ h)
 | .mp f a => .mp (weaken f) (weaken a)

def Boolean {ctx : Nat} (t : Term ctx) : Formula ctx := .disj (.equal t .zero) (.equal t (.succ .zero))
def graph {ctx : Nat} (tag : Nat) (t value : Term ctx) : Formula ctx :=
 .disj (.equal (unary tag t) .zero) (.conj (.equal t value) (.equal (unary tag t) (.succ .zero)))
theorem substUnary {m n : Nat} (sub : Fin m → Term n) tag (t : Term m) :
 substitute sub (unary tag t) = unary tag (substitute sub t) := by
 simp only [unary,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
theorem substGraph {m n : Nat} (sub : Fin m → Term n) tag (t v : Term m) :
 substituteFormula sub (graph tag t v) = graph tag (substitute sub t) (substitute sub v) := by
 simp only [graph,substituteFormula,substUnary,substitute]
noncomputable def unaryCongruence {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} tag (s t : Term ctx)
 (h : Hilbert.Local T ctx G (.equal s t)) : Hilbert.Local T ctx G (.equal (unary tag s) (unary tag t)) := by
 have d := localUnary (unary tag (.var 0)) s t h
 simpa only [substUnary,substitute,Fin.cases_zero] using d

theorem isZeroGraph {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨1,isZero⟩) (t : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (graph tag t .zero)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 obtain ⟨hz⟩ := isZeroZero (ctx := ctx) p tag ht
 have hzero : Derivation T (.imp (.equal t .zero) (graph tag t .zero)) := by
  have h : Hilbert.Local T ctx [.equal t .zero] (.equal t .zero) := .hypothesis List.mem_cons_self
  have he := localTrans _ _ _ (unaryCongruence tag t .zero h) (.base hz)
  exact Hilbert.Local.finish (Hilbert.Local.discharge
   (.mp (.base (.logical (.orRight _ _))) (.mp (.mp (.base (.logical (.andIntro _ _))) h) he)))
 let H := HistoryOrder.SupportProof.predBody t
 have h : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm t) (.succ (.var 0))) := .hypothesis List.mem_cons_self
 obtain ⟨hp⟩ := isZeroSucc p tag ht (.var (0 : Fin (ctx+1)))
 have he := localTrans _ _ _ (unaryCongruence tag (liftTerm t) (.succ (.var 0)) h) (.base hp)
 have hg : Hilbert.Local T (ctx+1) [H] (graph tag (liftTerm t) .zero) := .mp (.base (.logical (.orLeft _ _))) he
 have hbody : Derivation T (.imp H (GorbowPACore.weaken (graph tag t .zero))) := by
  simpa only [GorbowPACore.weaken,substGraph,substitute,liftTerm,renameTerm] using Hilbert.Local.finish (Hilbert.Local.discharge hg)
 obtain ⟨hpositive⟩ := HBQuantifier.existentialElimination T H (graph tag t .zero) ⟨hbody⟩
 obtain ⟨hsplit⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T t
 exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzero) hpositive) hsplit⟩

theorem isOneGraph {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨1,isOne⟩) (t : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (graph tag t (.succ .zero))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 obtain ⟨hz⟩ := isOneZero (ctx := ctx) p tag ht
 have hzero : Derivation T (.imp (.equal t .zero) (graph tag t (.succ .zero))) := by
  have h : Hilbert.Local T ctx [.equal t .zero] (.equal t .zero) := .hypothesis List.mem_cons_self
  have he := localTrans _ _ _ (unaryCongruence tag t .zero h) (.base hz)
  exact Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base (.logical (.orLeft _ _))) he))
 let H := HistoryOrder.SupportProof.predBody t
 let u := (Term.var (0 : Fin (ctx+1)))
 let z := unary (zeroChild tag) u
 let Q := graph tag (liftTerm t) (.succ .zero)
 have h : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm t) (.succ u)) := .hypothesis List.mem_cons_self
 obtain ⟨hs⟩ := isOneSucc p tag ht u
 have he := localTrans _ _ _ (unaryCongruence tag (liftTerm t) (.succ u) h) (.base hs)
 have hzcase : Hilbert.Local T (ctx+1) [H] (.imp (.equal z .zero) Q) := by
  have hz' : Hilbert.Local T (ctx+1) [.equal z .zero,H] (.equal z .zero) := .hypothesis List.mem_cons_self
  exact Hilbert.Local.discharge (.mp (.base (.logical (.orLeft _ _))) (localTrans _ _ _ (weaken he) hz'))
 have hocase : Hilbert.Local T (ctx+1) [H] (.imp (.conj (.equal u .zero) (.equal z (.succ .zero))) Q) := by
  have hh : Hilbert.Local T (ctx+1) [.conj (.equal u .zero) (.equal z (.succ .zero)),H]
    (.conj (.equal u .zero) (.equal z (.succ .zero))) := .hypothesis List.mem_cons_self
  have hu : Hilbert.Local T (ctx+1) [.conj (.equal u .zero) (.equal z (.succ .zero)),H] (.equal u .zero) := .mp (.base (.logical (.andLeft _ _))) hh
  have ho : Hilbert.Local T (ctx+1) [.conj (.equal u .zero) (.equal z (.succ .zero)),H] (.equal z (.succ .zero)) := .mp (.base (.logical (.andRight _ _))) hh
  have htone := localTrans _ _ _ (weaken h) (localUnary (.succ (.var 0)) u .zero hu)
  have hout := localTrans _ _ _ (weaken he) ho
  exact Hilbert.Local.discharge (.mp (.base (.logical (.orRight _ _))) (.mp (.mp (.base (.logical (.andIntro _ _))) htone) hout))
 obtain ⟨hg⟩ := isZeroGraph p _ (zeroInstalled p tag ht) u
 have result : Hilbert.Local T (ctx+1) [H] Q := .mp (.mp (.mp (.base (.logical (.orElim _ _ _))) hzcase) hocase) (.base hg)
 have hbody : Derivation T (.imp H (GorbowPACore.weaken (graph tag t (.succ .zero)))) := by
  simpa only [Q,GorbowPACore.weaken,substGraph,substitute,liftTerm,renameTerm] using Hilbert.Local.finish (Hilbert.Local.discharge result)
 obtain ⟨hpositive⟩ := HBQuantifier.existentialElimination T H (graph tag t (.succ .zero)) ⟨hbody⟩
 obtain ⟨hsplit⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T t
 exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzero) hpositive) hsplit⟩

theorem isOneIntro {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨1,isOne⟩) (t : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.imp (.equal t (.succ .zero)) (.equal (unary tag t) (.succ .zero)))) := by
 obtain ⟨ho⟩ := isOneOne (ctx := ctx) p tag ht
 have h : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx [.equal t (.succ .zero)] (.equal t (.succ .zero)) := .hypothesis List.mem_cons_self
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ (unaryCongruence tag t (.succ .zero) h) (.base ho)))⟩

theorem isOneBoolean {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨1,isOne⟩) (t : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (Boolean (unary tag t))) := by
 obtain ⟨hg⟩ := isOneGraph p tag ht t
 let T := GorbowPRNumeralCalculation.Theory p
 have hl : Derivation T (.imp (.equal (unary tag t) .zero) (Boolean (unary tag t))) := .logical (.orLeft _ _)
 have hr : Derivation T (.imp (.conj (.equal t (.succ .zero)) (.equal (unary tag t) (.succ .zero))) (Boolean (unary tag t))) :=
  Hilbert.compose (.logical (.orRight _ _)) (.logical (.andRight _ _))
 exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hl) hr) hg⟩

theorem isOneElim {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨1,isOne⟩) (t : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.imp (.equal (unary tag t) (.succ .zero)) (.equal t (.succ .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := Formula.equal (unary tag t) (.succ .zero)
 have h : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have hl : Hilbert.Local T ctx [H] (.imp (.equal (unary tag t) .zero) (.equal t (.succ .zero))) := by
  have hz : Hilbert.Local T ctx [.equal (unary tag t) .zero,H] (.equal (unary tag t) .zero) := .hypothesis List.mem_cons_self
  have bad := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (weaken h)) hz
  exact Hilbert.Local.discharge (Hilbert.Local.explosion _ bad (.base (.arithmetic (.succNotZero .zero))))
 have hr : Hilbert.Local T ctx [H] (.imp (.conj (.equal t (.succ .zero)) H) (.equal t (.succ .zero))) := .base (.logical (.andLeft _ _))
 obtain ⟨hg⟩ := isOneGraph p tag ht t
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.mp (.mp (.base (.logical (.orElim _ _ _))) hl) hr) (.base hg)))⟩
noncomputable def binaryCongruence {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} tag (s t u : Term ctx)
 (h : Hilbert.Local T ctx G (.equal s t)) : Hilbert.Local T ctx G (.equal (binary tag s u) (binary tag t u)) := by
 have d := localUnary (binary tag (.var 0) (liftTerm u)) s t h
 simpa only [binary,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,Fin.cases_zero,liftTerm,Support.shiftCancel] using d

noncomputable def booleanTransport {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} (s t : Term ctx)
 (he : Hilbert.Local T ctx G (.equal s t)) (hb : Hilbert.Local T ctx G (Boolean t)) : Hilbert.Local T ctx G (Boolean s) := by
 have hz : Hilbert.Local T ctx G (.imp (.equal t .zero) (Boolean s)) := by
  have h : Hilbert.Local T ctx (.equal t .zero :: G) (.equal t .zero) := .hypothesis List.mem_cons_self
  exact Hilbert.Local.discharge (.mp (.base (.logical (.orLeft _ _))) (localTrans _ _ _ (weaken he) h))
 have ho : Hilbert.Local T ctx G (.imp (.equal t (.succ .zero)) (Boolean s)) := by
  have h : Hilbert.Local T ctx (.equal t (.succ .zero) :: G) (.equal t (.succ .zero)) := .hypothesis List.mem_cons_self
  exact Hilbert.Local.discharge (.mp (.base (.logical (.orRight _ _))) (localTrans _ _ _ (weaken he) h))
 exact .mp (.mp (.mp (.base (.logical (.orElim _ _ _))) hz) ho) hb

theorem orBoolean {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,leftOr⟩) (previous current : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (Boolean previous) (.imp (Boolean current) (Boolean (binary tag previous current))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let G := [Boolean current,Boolean previous]
 have hb : Hilbert.Local T ctx G (Boolean previous) := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hc : Hilbert.Local T ctx G (Boolean current) := .hypothesis List.mem_cons_self
 obtain ⟨hz⟩ := orZero p tag ht current
 obtain ⟨ho⟩ := Equations.orOne p tag ht current
 have hzero : Hilbert.Local T ctx G (.imp (.equal previous .zero) (Boolean (binary tag previous current))) := by
  have h : Hilbert.Local T ctx (.equal previous .zero :: G) (.equal previous .zero) := .hypothesis List.mem_cons_self
  exact Hilbert.Local.discharge (booleanTransport _ _ (localTrans _ _ _ (binaryCongruence tag previous .zero current h) (.base hz)) (weaken hc))
 have hone : Hilbert.Local T ctx G (.imp (.equal previous (.succ .zero)) (Boolean (binary tag previous current))) := by
  have h : Hilbert.Local T ctx (.equal previous (.succ .zero) :: G) (.equal previous (.succ .zero)) := .hypothesis List.mem_cons_self
  exact Hilbert.Local.discharge (.mp (.base (.logical (.orRight _ _))) (localTrans _ _ _ (binaryCongruence tag previous (.succ .zero) current h) (.base ho)))
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
  (.mp (.mp (.mp (.base (.logical (.orElim _ _ _))) hzero) hone) hb)))⟩

theorem orRightIntro {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,leftOr⟩) (previous current : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (Boolean previous) (.imp (.equal current (.succ .zero)) (.equal (binary tag previous current) (.succ .zero))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let G := [Formula.equal current (.succ .zero),Boolean previous]
 have hb : Hilbert.Local T ctx G (Boolean previous) := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hc : Hilbert.Local T ctx G (.equal current (.succ .zero)) := .hypothesis List.mem_cons_self
 obtain ⟨hz⟩ := orZero p tag ht current
 obtain ⟨ho⟩ := Equations.orOne p tag ht current
 have hzero : Hilbert.Local T ctx G (.imp (.equal previous .zero) (.equal (binary tag previous current) (.succ .zero))) := by
  have h : Hilbert.Local T ctx (.equal previous .zero :: G) (.equal previous .zero) := .hypothesis List.mem_cons_self
  exact Hilbert.Local.discharge (localTrans _ _ _ (localTrans _ _ _ (binaryCongruence tag previous .zero current h) (.base hz)) (weaken hc))
 have hone : Hilbert.Local T ctx G (.imp (.equal previous (.succ .zero)) (.equal (binary tag previous current) (.succ .zero))) := by
  have h : Hilbert.Local T ctx (.equal previous (.succ .zero) :: G) (.equal previous (.succ .zero)) := .hypothesis List.mem_cons_self
  exact Hilbert.Local.discharge (localTrans _ _ _ (binaryCongruence tag previous (.succ .zero) current h) (.base ho))
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
  (.mp (.mp (.mp (.base (.logical (.orElim _ _ _))) hzero) hone) hb)))⟩

theorem orSplit {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,leftOr⟩) (previous current : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (Boolean previous) (.imp (.equal (binary tag previous current) (.succ .zero))
   (.disj (.equal previous (.succ .zero)) (.equal current (.succ .zero)))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let G := [Formula.equal (binary tag previous current) (.succ .zero),Boolean previous]
 let Q := Formula.disj (.equal previous (.succ .zero)) (.equal current (.succ .zero))
 have hb : Hilbert.Local T ctx G (Boolean previous) := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hc : Hilbert.Local T ctx G (.equal (binary tag previous current) (.succ .zero)) := .hypothesis List.mem_cons_self
 obtain ⟨hz⟩ := orZero p tag ht current
 have hzero : Hilbert.Local T ctx G (.imp (.equal previous .zero) Q) := by
  have h : Hilbert.Local T ctx (.equal previous .zero :: G) (.equal previous .zero) := .hypothesis List.mem_cons_self
  have he := localTrans _ _ _ (binaryCongruence tag previous .zero current h) (.base hz)
  exact Hilbert.Local.discharge (.mp (.base (.logical (.orRight _ _)))
   (localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ he) (weaken hc)))
 have hone : Hilbert.Local T ctx G (.imp (.equal previous (.succ .zero)) Q) := .base (.logical (.orLeft _ _))
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
  (.mp (.mp (.mp (.base (.logical (.orElim _ _ _))) hzero) hone) hb)))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.NormalizerProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.NormalizerProof
