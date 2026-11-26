module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.ConstructorSupportProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.ReferenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherSupportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowFormulaSubstitution GorbowSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix HistoryCodec.ArithmeticSupport

def Computes {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx)) (q : Program arity)
    (args : List.Vector (Term ctx) arity) (value : Term ctx) : Prop :=
  ∀ tag, (nodes p)[tag]? = some ⟨arity,q⟩ → Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.equal (call tag args) value))
theorem liftClosed {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx)) (q : Program arity)
    (args : List.Vector (Term ctx) arity) (value : Term ctx)
    (h : ConstructorSupportProof.Computes p q args value) : Computes p G q args value := by
  intro tag ht
  obtain ⟨he⟩ := h tag ht
  exact ⟨.base he⟩

noncomputable def congruentTerms {T : Sentence → Prop} {n ctx : Nat} {G : List (Formula ctx)} (s t : Fin n → Term ctx)
    (hs : ∀ i, Hilbert.Local T ctx G (.equal (s i) (t i))) :
    ∀ f : Term n, Hilbert.Local T ctx G (.equal (substitute s f) (substitute t f)) := by
  intro f
  induction f with
  | var i => exact hs i
  | zero => exact .base (.logical (.reflexive .zero))
  | succ f ih => exact localUnary (.succ (.var 0)) _ _ ih
  | universalFunction f ih => exact localUnary (.universalFunction (.var 0)) _ _ ih
  | add f g hf hg =>
    have h1 := localUnary (.add (.var 0) (renameTerm Fin.succ (substitute s g))) _ _ hf
    have h2 := localUnary (.add (renameTerm Fin.succ (substitute t f)) (.var 0)) _ _ hg
    simp only [substitute,Support.shiftCancel] at h1 h2
    exact localTrans _ _ _ h1 h2
  | mul f g hf hg =>
    have h1 := localUnary (.mul (.var 0) (renameTerm Fin.succ (substitute s g))) _ _ hf
    have h2 := localUnary (.mul (renameTerm Fin.succ (substitute t f)) (.var 0)) _ _ hg
    simp only [substitute,Support.shiftCancel] at h1 h2
    exact localTrans _ _ _ h1 h2
noncomputable def callCongruence {T : Sentence → Prop} {arity ctx : Nat} {G : List (Formula ctx)} (tag : Nat)
    (args others : List.Vector (Term ctx) arity)
    (h : ∀ i, Hilbert.Local T ctx G (.equal (args.get i) (others.get i))) :
    Hilbert.Local T ctx G (.equal (call tag args) (call tag others)) := by
  have d := congruentTerms args.get others.get h (call tag (argumentVariables arity))
  rw [Logic.substCall,Logic.substArguments,Logic.substCall,Logic.substArguments] at d
  exact d

theorem compose {n arity k ctx : Nat} (p : Program n) (G : List (Formula ctx)) (f : Program k) (g : Fin k → Program arity)
    (args : List.Vector (Term ctx) arity) (values : List.Vector (Term ctx) k) (value : Term ctx)
    (hg : ∀ i, Computes p G (g i) args (values.get i))
    (hf : Computes p G f values value) : Computes p G (.composition f g) args value := by
  intro tag ht
  obtain ⟨he⟩ := GorbowPRSymbolicEquations.Proof.compositionEquation n p tag arity k f g ht ctx args
  have hall : ∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
      (.equal (call (tag+argumentTag f g i) args) (values.get i))) :=
    fun i => hg i _ (SixSol20261112.Fuel.Equations.argumentChild p tag f g ht i)
  -- Vector congruence is a finite internal congruence proof, not evaluation.
  obtain ⟨hfun⟩ := hf (tag+1) (SixSol20261112.Fuel.Equations.functionChild p tag f g ht)
  let original := List.Vector.ofFn (fun i => call (tag+argumentTag f g i) args)
  have hcg : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
      (.equal (call (tag+1) original) (call (tag+1) values)) := by
    apply callCongruence
    intro i
    simpa only [original,List.Vector.get_ofFn] using Classical.choice (hall i)
  exact ⟨localTrans _ _ _ (.base he) (localTrans _ _ _ hcg hfun)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherSupportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherSupportProof
