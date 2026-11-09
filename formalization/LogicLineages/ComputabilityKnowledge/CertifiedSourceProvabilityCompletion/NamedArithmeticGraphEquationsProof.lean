module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.NamedArithmeticGraphSupportProof

@[expose] public section
/-! Arbitrary-term original node equations over literal finite node support.
This is ordinary Hilbert specialization only, independent of the arithmetic
proof transfer and of any assertion that a program satisfies its graph. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.NamedArithmeticGraph.Equations
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof
open GorbowSubstitution List.Vector

private theorem subCall {ctx out arity : Nat} (tag : Nat)
    (args : List.Vector (Term ctx) arity) (sigma : Fin ctx → Term out) :
    substitute sigma (call tag args) = call tag (args.map (substitute sigma)) :=
  GorbowPRCallCongruence.Proof.callSubstitution ctx out arity tag args sigma

private theorem subArguments {arity ctx : Nat} (args : List.Vector (Term ctx) arity) :
    (argumentVariables arity).map (substitute args.get) = args := by
  apply List.Vector.ext
  intro i
  simp only [List.Vector.get_map,argumentVariables,List.Vector.get_ofFn,substitute]

private theorem subTail {arity ctx : Nat} (x : Term ctx) (args : List.Vector (Term ctx) arity) :
    (tailVariables arity).map (substitute (Fin.cases x args.get)) = args := by
  apply List.Vector.ext
  intro i
  simp only [List.Vector.get_map,tailVariables,List.Vector.get_ofFn,substitute,Fin.cases_succ]

private theorem subCalls {ctx out arity k : Nat} (tags : Fin k → Nat)
    (args : List.Vector (Term ctx) arity) (sigma : Fin ctx → Term out) :
    (List.Vector.ofFn (fun i => call (tags i) args)).map (substitute sigma) =
      List.Vector.ofFn (fun i => call (tags i) (args.map (substitute sigma))) := by
  apply List.Vector.ext
  intro i
  simp only [List.Vector.get_map,List.Vector.get_ofFn,subCall]

theorem zero (tag ctx : Nat) :
    Nonempty (Derivation (Support.Theory Program.zero tag)
      (.equal (call (ctx := ctx) tag List.Vector.nil) .zero)) := by
  have h := Support.nodeEquationInstance Program.zero tag
    (call tag (List.Vector.nil : List.Vector (Term 0) 0)) .zero
    List.mem_cons_self (Fin.elim0 : Fin 0 → Term ctx)
  simpa only [subCall,List.Vector.map_nil,substitute] using h

theorem successor (tag ctx : Nat) (args : List.Vector (Term ctx) 1) :
    Nonempty (Derivation (Support.Theory Program.succ tag)
      (.equal (call tag args) (.succ (args.get 0)))) := by
  have h := Support.nodeEquationInstance Program.succ tag
    (call tag (argumentVariables 1)) (.succ (.var 0)) List.mem_cons_self args.get
  simpa only [subCall,subArguments,substitute] using h

theorem projection {arity : Nat} (i : Fin arity) (tag ctx : Nat)
    (args : List.Vector (Term ctx) arity) :
    Nonempty (Derivation (Support.Theory (Program.projection i) tag)
      (.equal (call tag args) (args.get i))) := by
  have h := Support.nodeEquationInstance (Program.projection i) tag
    (call tag (argumentVariables arity)) (.var i) List.mem_cons_self args.get
  simpa only [subCall,subArguments,substitute] using h

theorem composition {m k : Nat} (f : Program k) (g : Fin k → Program m)
    (tag ctx : Nat) (args : List.Vector (Term ctx) m) :
    Nonempty (Derivation (Support.Theory (Program.composition f g) tag)
      (.equal (call tag args)
        (call (tag+1) (List.Vector.ofFn fun i => call (tag+argumentTag f g i) args)))) := by
  have h := Support.nodeEquationInstance (Program.composition f g) tag
    (call tag (argumentVariables m))
    (call (tag+1) (List.Vector.ofFn fun i => call (tag+argumentTag f g i) (argumentVariables m)))
    List.mem_cons_self args.get
  simpa only [subCall,subArguments,subCalls] using h

theorem recursionZero {m : Nat} (f : Program m) (g : Program (m+2))
    (tag ctx : Nat) (args : List.Vector (Term ctx) m) :
    Nonempty (Derivation (Support.Theory (Program.recursion f g) tag)
      (.equal (call tag (.zero ::ᵥ args)) (call (tag+1) args))) := by
  have h := Support.nodeEquationInstance (Program.recursion f g) tag
    (call tag (.zero ::ᵥ argumentVariables m)) (call (tag+1) (argumentVariables m))
    List.mem_cons_self args.get
  simpa only [subCall,List.Vector.map_cons,subArguments,substitute] using h

theorem recursionSuccessor {m : Nat} (f : Program m) (g : Program (m+2))
    (tag ctx : Nat) (x : Term ctx) (args : List.Vector (Term ctx) m) :
    Nonempty (Derivation (Support.Theory (Program.recursion f g) tag)
      (.equal (call tag (.succ x ::ᵥ args))
        (call (tag+stepTag f) (x ::ᵥ call tag (x ::ᵥ args) ::ᵥ args)))) := by
  have h := Support.nodeEquationInstance (Program.recursion f g) tag
    (call tag (.succ (.var 0) ::ᵥ tailVariables m))
    (call (tag+stepTag f) (.var 0 ::ᵥ call tag (.var 0 ::ᵥ tailVariables m) ::ᵥ tailVariables m))
    (List.mem_cons_of_mem _ List.mem_cons_self) (Fin.cases x args.get)
  simpa only [subCall,List.Vector.map_cons,subTail,substitute,Fin.cases_zero] using h

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.NamedArithmeticGraph.Equations
