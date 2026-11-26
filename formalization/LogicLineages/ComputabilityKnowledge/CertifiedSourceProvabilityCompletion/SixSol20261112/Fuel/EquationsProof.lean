module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.LogicProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRChildTagsProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRSubtreeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.Equations
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPRDefiningEquations
open GorbowPRChildTags GorbowFormulaSubstitution GorbowSubstitution List.Vector
open NamedArithmeticGraph

theorem functionChild {n m k : Nat} (p : Program n) (tag : Nat)
    (f : Program k) (g : Fin k → Program m)
    (h : (nodes p)[tag]? = some ⟨m,Program.composition f g⟩) :
    (nodes p)[tag+1]? = some ⟨k,f⟩ :=
  GorbowPRSubtree.Proof.lookupTransport n p tag ⟨m,Program.composition f g⟩ 1 ⟨k,f⟩ h
    (GorbowPRChildTags.Proof.compositionFunction m k f g)

theorem argumentChild {n m k : Nat} (p : Program n) (tag : Nat)
    (f : Program k) (g : Fin k → Program m)
    (h : (nodes p)[tag]? = some ⟨m,Program.composition f g⟩) (i : Fin k) :
    (nodes p)[tag+argumentTag f g i]? = some ⟨m,g i⟩ :=
  GorbowPRSubtree.Proof.lookupTransport n p tag ⟨m,Program.composition f g⟩
    (argumentTag f g i) ⟨m,g i⟩ h (GorbowPRChildTags.Proof.compositionArgument m k f g i)

theorem recursionStepChild {n m : Nat} (p : Program n) tag (f : Program m) (g : Program (m+2))
    (h : (nodes p)[tag]? = some ⟨m+1,Program.recursion f g⟩) :
    (nodes p)[tag+stepTag f]? = some ⟨m+2,g⟩ :=
  GorbowPRSubtree.Proof.lookupTransport n p tag ⟨m+1,Program.recursion f g⟩
    (stepTag f) ⟨m+2,g⟩ h (GorbowPRChildTags.Proof.recursionStep m f g)

theorem projection {n arity ctx : Nat} (p : Program n) tag (i : Fin arity)
    (h : (nodes p)[tag]? = some ⟨arity,Program.projection i⟩)
    (args : List.Vector (Term ctx) arity) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call tag args) (args.get i))) :=
  Support.intoRegistry p (Program.projection i) tag h _
    (NamedArithmeticGraph.Equations.projection i tag ctx args)

/-- Composition is normalized using ACTUAL already derived child equations.
The public endpoints below discharge every such child proof explicitly. -/
theorem compositionValues {n m k ctx : Nat} (p : Program n) tag
    (f : Program k) (g : Fin k → Program m)
    (h : (nodes p)[tag]? = some ⟨m,Program.composition f g⟩)
    (args : List.Vector (Term ctx) m) (values : List.Vector (Term ctx) k)
    (hv : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (tag+argumentTag f g i) args) (values.get i)))) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag args) (call (tag+1) values))) := by
  obtain ⟨hc⟩ := GorbowPRSymbolicEquations.Proof.compositionEquation n p tag m k f g h ctx args
  have he := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) (tag+1)
    (List.Vector.ofFn fun i => call (tag+argumentTag f g i) args) values
    (fun i => by simpa only [List.Vector.get_ofFn] using Classical.choice (hv i))
  exact ⟨Logic.trans _ _ _ hc he⟩

theorem compositionProjections {n m k ctx : Nat} (p : Program n) tag
    (f : Program k) (g : Fin k → Program m)
    (h : (nodes p)[tag]? = some ⟨m,Program.composition f g⟩)
    (indices : Fin k → Fin m) (hg : ∀ i, g i = Program.projection (indices i))
    (args : List.Vector (Term ctx) m) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag args) (call (tag+1) (List.Vector.ofFn fun i => args.get (indices i))))) := by
  apply compositionValues p tag f g h args
  intro i
  have hi := argumentChild p tag f g h i
  rw [hg i] at hi
  simpa only [List.Vector.get_ofFn] using projection p (tag+argumentTag f g i) (indices i) hi args

private def outerIndex : Fin 5 → Fin 5 :=
  Fin.cases 1 (Fin.cases 0 (Fin.cases 2 (Fin.cases 3 (Fin.cases 4 Fin.elim0))))

private theorem outerProjection (i : Fin 5) : outerArguments i = Program.projection (outerIndex i) := by
  cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
    | zero => rfl
    | succ i => cases i using Fin.cases with
      | zero => rfl
      | succ i => cases i using Fin.cases with
        | zero => rfl
        | succ i => cases i using Fin.cases with
          | zero => rfl
          | succ i => exact Fin.elim0 i

private theorem outerVector {ctx : Nat} (index fuel context formula cert : Term ctx) :
    (List.Vector.ofFn fun i => (inputs index fuel context formula cert).get (outerIndex i)) =
      fuel ::ᵥ index ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil := by
  apply List.Vector.ext
  intro i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
    | zero => rfl
    | succ i => cases i using Fin.cases with
      | zero => rfl
      | succ i => cases i using Fin.cases with
        | zero => rfl
        | succ i => cases i using Fin.cases with
          | zero => rfl
          | succ i => exact Fin.elim0 i

theorem verifierEquation {n ctx : Nat} (p : Program n) tag (q0 : Program 5)
    (h : (nodes p)[tag]? = some ⟨5,verifier q0⟩)
    (index fuel context formula cert : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (inputs index fuel context formula cert))
        (call (tag+1) (fuel ::ᵥ index ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil)))) := by
  have hd := compositionProjections p tag (accumulator q0) outerArguments h
    outerIndex outerProjection (inputs index fuel context formula cert)
  simpa only [outerVector] using hd

/-- The source equation leftOr(1,x)=1, independent of opaque x. -/
theorem orOne {n ctx : Nat} (p : Program n) tag
    (h : (nodes p)[tag]? = some ⟨2,leftOr⟩) (x : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (Term.numeral 1 ::ᵥ x ::ᵥ nil)) (Term.numeral 1))) := by
  let f := Program.projection (0 : Fin 1)
  let g : Program 3 := Program.composition Program.succ (fun _ => Program.projection (0 : Fin 3))
  let gt := tag+stepTag f
  have hg : (nodes p)[gt]? = some ⟨3,g⟩ := recursionStepChild p tag f g h
  obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation
    n p tag 1 f g h ctx .zero (x ::ᵥ nil)
  let args : List.Vector (Term ctx) 3 := .zero ::ᵥ call tag (.zero ::ᵥ x ::ᵥ nil) ::ᵥ x ::ᵥ nil
  obtain ⟨hc⟩ := compositionProjections p gt Program.succ
    (fun _ : Fin 1 => Program.projection (0 : Fin 3)) hg
    (fun _ => (0 : Fin 3)) (fun _ => rfl) args
  have hsucc := functionChild p gt Program.succ (fun _ : Fin 1 => Program.projection (0 : Fin 3)) hg
  obtain ⟨hs⟩ := Support.intoRegistry p Program.succ (gt+1) hsucc _
    (NamedArithmeticGraph.Equations.successor (gt+1) ctx (.zero ::ᵥ nil))
  have hc' : Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call gt args) (call (gt+1) (.zero ::ᵥ nil))) := hc
  have hr' : Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (.succ .zero ::ᵥ x ::ᵥ nil)) (call gt args)) := hr
  change Nonempty (Derivation _ (.equal (call tag (.succ .zero ::ᵥ x ::ᵥ nil)) (.succ .zero)))
  exact ⟨Logic.trans _ _ _ hr' (Logic.trans _ _ _ hc' hs)⟩

private def firstOneTemplate {ctx : Nat} (tag : Nat) (x : Term ctx) : Formula (ctx+1) :=
  .equal (call tag (.var 0 ::ᵥ liftTerm x ::ᵥ nil)) (Term.numeral 1)

private theorem firstOneAt {ctx : Nat} (tag : Nat) (x t : Term ctx) :
    GorbowStandardInstances.instantiate (firstOneTemplate tag x) t =
      .equal (call tag (t ::ᵥ x ::ᵥ nil)) (Term.numeral 1) := by
  simp only [GorbowStandardInstances.instantiate,firstOneTemplate,liftTerm,substituteFormula,
    Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,Support.shiftCancel,
    substitute,Fin.cases_zero,Logic.substNumeral]

theorem orOneRule {n ctx : Nat} (p : Program n) tag
    (h : (nodes p)[tag]? = some ⟨2,leftOr⟩) (previous current : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (.equal previous (Term.numeral 1))
        (.equal (call tag (previous ::ᵥ current ::ᵥ nil)) (Term.numeral 1)))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  obtain ⟨hone⟩ := orOne p tag h current
  have hr := Derivation.logical (A := T)
    (.equalityReplace (firstOneTemplate tag current) (Term.numeral 1) previous)
  rw [GorbowPACore.logicalFormula,firstOneAt,firstOneAt] at hr
  have hh : Hilbert.Local T ctx [.equal previous (Term.numeral 1)]
      (.equal previous (Term.numeral 1)) := .hypothesis List.mem_cons_self
  have hs := Hilbert.Local.mp (.base (Logic.symmetryRule T previous (Term.numeral 1))) hh
  have hd := Hilbert.Local.mp (Hilbert.Local.mp (.base hr) hs) (.base hone)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hd)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.Equations
