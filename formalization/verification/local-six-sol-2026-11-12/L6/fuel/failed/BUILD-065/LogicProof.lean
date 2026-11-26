module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.NamedArithmeticGraphEquationsProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.HBQuantifierSupportProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.Logic
open GorbowSyntax GorbowTheoryProof GorbowFormulaSubstitution GorbowSubstitution
open GorbowPRDefiningEquations List.Vector
open NamedArithmeticGraph

theorem substNumeral {m n : Nat} (sub : Fin m → Term n) (k : Nat) :
    substitute sub (Term.numeral k) = Term.numeral k :=
  GorbowHeaderSubstitutionProof.numerals m n sub k

theorem substCall {m n arity : Nat} (sub : Fin m → Term n) (tag : Nat)
    (args : List.Vector (Term m) arity) :
    substitute sub (call tag args) = call tag (args.map (substitute sub)) :=
  GorbowPRCallCongruence.Proof.callSubstitution m n arity tag args sub

def trans {T : Sentence → Prop} {ctx : Nat} (s t u : Term ctx)
    (hst : Derivation T (.equal s t)) (htu : Derivation T (.equal t u)) :
    Derivation T (.equal s u) := by
  have h := Derivation.logical (A := T)
    (.equalityReplace (.equal (renameTerm Fin.succ s) (.var 0)) t u)
  change Derivation T (.imp (.equal t u)
    (.imp (.equal (substitute (Fin.cases t Term.var) (renameTerm Fin.succ s)) t)
      (.equal (substitute (Fin.cases u Term.var) (renameTerm Fin.succ s)) u))) at h
  rw [Support.shiftCancel,Support.shiftCancel] at h
  exact .mp (.mp h htu) hst

def unary {T : Sentence → Prop} {ctx : Nat} (f : Term (ctx+1)) (s t : Term ctx)
    (h : Derivation T (.equal s t)) :
    Derivation T (.equal (substitute (Fin.cases s Term.var) f)
      (substitute (Fin.cases t Term.var) f)) := by
  let fs := substitute (Fin.cases s Term.var) f
  let phi := Formula.equal (renameTerm Fin.succ fs) f
  have hi : Derivation T (GorbowStandardInstances.instantiate phi s) := by
    change Derivation T (.equal (substitute (Fin.cases s Term.var) (renameTerm Fin.succ fs)) fs)
    rw [Support.shiftCancel]
    exact .logical (.reflexive fs)
  have hr : Derivation T (GorbowStandardInstances.instantiate phi t) :=
    .mp (.mp (.logical (.equalityReplace phi s t)) h) hi
  change Derivation T (.equal (substitute (Fin.cases t Term.var) (renameTerm Fin.succ fs))
    (substitute (Fin.cases t Term.var) f)) at hr
  rw [Support.shiftCancel] at hr
  exact hr

def congruentTerms (T : Sentence → Prop) {n ctx : Nat} (s t : Fin n → Term ctx)
    (hs : ∀ i, Derivation T (.equal (s i) (t i))) :
    ∀ f : Term n, Derivation T (.equal (substitute s f) (substitute t f)) := by
  intro f
  induction f with
  | var i => exact hs i
  | zero => exact .logical (.reflexive .zero)
  | succ f ih => exact unary (.succ (.var 0)) _ _ ih
  | universalFunction f ih => exact unary (.universalFunction (.var 0)) _ _ ih
  | add f g hf hg =>
      have h1 := unary (.add (.var 0) (renameTerm Fin.succ (substitute s g))) _ _ hf
      have h2 := unary (.add (renameTerm Fin.succ (substitute t f)) (.var 0)) _ _ hg
      simp only [substitute,Support.shiftCancel] at h1 h2
      exact trans _ _ _ h1 h2
  | mul f g hf hg =>
      have h1 := unary (.mul (.var 0) (renameTerm Fin.succ (substitute s g))) _ _ hf
      have h2 := unary (.mul (renameTerm Fin.succ (substitute t f)) (.var 0)) _ _ hg
      simp only [substitute,Support.shiftCancel] at h1 h2
      exact trans _ _ _ h1 h2

theorem substArguments {arity ctx : Nat} (args : List.Vector (Term ctx) arity) :
    (argumentVariables arity).map (substitute args.get) = args := by
  apply List.Vector.ext
  intro i
  simp only [List.Vector.get_map,argumentVariables,List.Vector.get_ofFn,substitute]

def callCongruence (T : Sentence → Prop) {arity ctx : Nat} (tag : Nat)
    (args others : List.Vector (Term ctx) arity)
    (h : ∀ i, Derivation T (.equal (args.get i) (others.get i))) :
    Derivation T (.equal (call tag args) (call tag others)) := by
  have d := congruentTerms T args.get others.get h (call tag (argumentVariables arity))
  rw [substCall,substArguments,substCall,substArguments] at d
  exact d

theorem oneInstance {ctx : Nat} (t : Term ctx) :
    GorbowStandardInstances.instantiate (.equal (.var 0) (Term.numeral 1) : Formula (ctx+1)) t =
      .equal t (Term.numeral 1) := by
  simp only [GorbowStandardInstances.instantiate,substituteFormula,substitute,
    Fin.cases_zero,substNumeral]

def oneTransport {T : Sentence → Prop} {ctx : Nat} (s t : Term ctx)
    (h : Derivation T (.equal s t)) :
    Derivation T (.imp (.equal s (Term.numeral 1)) (.equal t (Term.numeral 1))) := by
  have d := Derivation.logical (A := T)
    (.equalityReplace (.equal (.var 0) (Term.numeral 1) : Formula (ctx+1)) s t)
  rw [GorbowPACore.logicalFormula,oneInstance,oneInstance] at d
  exact .mp d h

def symmetryRule (T : Sentence → Prop) {ctx : Nat} (s t : Term ctx) :
    Derivation T (.imp (.equal s t) (.equal t s)) := by
  have h := Derivation.logical (A := T) (.equalityReplace (Support.equalityRightTemplate s) s t)
  rw [GorbowPACore.logicalFormula,Support.equalityRightInstance,Support.equalityRightInstance] at h
  have hd : Hilbert.Local T ctx [.equal s t] (.equal t s) :=
    .mp (.mp (.base h) (.hypothesis List.mem_cons_self)) (.base (.logical (.reflexive s)))
  exact Hilbert.Local.finish (Hilbert.Local.discharge hd)

def closeAll {T : Sentence → Prop} : ∀ {n : Nat} {phi : Formula n},
    Derivation T phi → Derivation T (GorbowStandardInduction.universalClosure phi)
  | 0,_,h => h
  | n+1,phi,h => closeAll (n := n) (phi := .all phi) (.generalize h)

private theorem liftVariables (n : Nat) : liftSubstitute (Term.var : Fin n → Term n) = Term.var := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

theorem formulaIdentity {n : Nat} (phi : Formula n) : substituteFormula Term.var phi = phi := by
  induction phi <;> simp only [substituteFormula,substitute_variables,liftVariables,*]

/-- Ordinary universal elimination in one added variable. This is derived
from the existing substitution theorem and allInstantiate, not a new rule. -/
theorem openAll (T : Sentence → Prop) {ctx : Nat} (phi : Formula (ctx+1))
    (h : Nonempty (Derivation T (.all phi))) : Nonempty (Derivation T phi) := by
  obtain ⟨hl⟩ := GorbowDerivationSubstitution.Proof.derivationSubstitution T ctx (ctx+1)
    (.all phi) (fun i => Term.var i.succ) h
  have hr := Derivation.mp (Derivation.logical (A := T)
    (.allInstantiate (substituteFormula (liftSubstitute (fun i : Fin ctx =>
      (Term.var i.succ : Term (ctx+1)))) phi) (.var 0))) hl
  have he : GorbowStandardInstances.instantiate
      (substituteFormula (liftSubstitute (fun i : Fin ctx => (Term.var i.succ : Term (ctx+1)))) phi)
      (.var 0) = phi := by
    unfold GorbowStandardInstances.instantiate
    rw [GorbowFormulaCompositionProof.composition]
    have hi : (fun i : Fin (ctx+1) => substitute
        (Fin.cases (.var 0) Term.var : Fin (ctx+2) → Term (ctx+1))
        (liftSubstitute (fun j : Fin ctx => (Term.var j.succ : Term (ctx+1))) i)) = Term.var := by
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i => rfl
    rw [hi,formulaIdentity]
  exact ⟨he ▸ hr⟩

def fuelTemplate {ctx : Nat} (tag : Nat) (index context formula cert : Term ctx) : Formula (ctx+1) :=
  success tag (liftTerm index) (.var 0) (liftTerm context) (liftTerm formula) (liftTerm cert)

theorem fuelTemplateAt {ctx : Nat} (tag : Nat) (index context formula cert s : Term ctx) :
    GorbowStandardInstances.instantiate (fuelTemplate tag index context formula cert) s =
      success tag index s context formula cert := by
  simp only [GorbowStandardInstances.instantiate,fuelTemplate,success,inputs,liftTerm,
    substituteFormula,substCall,List.Vector.map_cons,List.Vector.map_nil,
    Support.shiftCancel,substitute,Fin.cases_zero,substNumeral]

def fuelEqualityRule (T : Sentence → Prop) {ctx : Nat} (tag : Nat)
    (index context formula cert s t : Term ctx) :
    Derivation T (.imp (.equal s t) (.imp (success tag index s context formula cert)
      (success tag index t context formula cert))) := by
  have h := Derivation.logical (A := T)
    (.equalityReplace (fuelTemplate tag index context formula cert) s t)
  rw [GorbowPACore.logicalFormula,fuelTemplateAt,fuelTemplateAt] at h
  exact h

def fuelTransport {T : Sentence → Prop} {ctx : Nat} (tag : Nat)
    (index context formula cert s t : Term ctx) (h : Derivation T (.equal s t)) :
    Derivation T (.imp (success tag index s context formula cert)
      (success tag index t context formula cert)) :=
  .mp (fuelEqualityRule T tag index context formula cert s t) h

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.Logic
