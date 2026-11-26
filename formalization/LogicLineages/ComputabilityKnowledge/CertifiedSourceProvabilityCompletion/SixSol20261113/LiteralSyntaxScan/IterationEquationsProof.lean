module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.IterationTargets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.OperationalSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.IterationEquationsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix HistoryCodec.ArithmeticSupport Iteration
def tickTag (tag : Nat) : Nat := tag + stepTag (.projection (0 : Fin 1)) + 1

theorem tickInstalled {n : Nat} (p : Program n) tag
 (ht : (nodes p)[tag]? = some ⟨2,iterator⟩) :
 (nodes p)[tickTag tag]? = some ⟨1,tick⟩ := by
 have hs := Equations.recursionStepChild p tag (.projection (0 : Fin 1))
  (applyOne tick (.projection 1)) ht
 exact Equations.functionChild p _ tick (fun _ : Fin 1 => .projection (1 : Fin 3)) hs

theorem zero {n ctx : Nat} (p : Program n) tag
 (ht : (nodes p)[tag]? = some ⟨2,iterator⟩) (state : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (runCall tag .zero state) state)) := by
 obtain ⟨h⟩ := OperationalSupportProof.iteratorZero p [] state tag ht
 exact ⟨Hilbert.Local.finish h⟩

theorem successor {n ctx : Nat} (p : Program n) tag
 (ht : (nodes p)[tag]? = some ⟨2,iterator⟩) (count state : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (runCall tag (.succ count) state)
   (call (tickTag tag) (runCall tag count state ::ᵥ nil)))) := by
 have hs := Equations.recursionStepChild p tag (.projection (0 : Fin 1))
  (applyOne tick (.projection 1)) ht
 obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p tag 1
  (.projection (0 : Fin 1)) (applyOne tick (.projection 1)) ht ctx count (state ::ᵥ nil)
 obtain ⟨hc⟩ := Equations.compositionProjections p
  (tag + stepTag (.projection (0 : Fin 1))) tick
  (fun _ : Fin 1 => .projection (1 : Fin 3)) hs (fun _ => (1 : Fin 3))
  (fun _ => rfl) (count ::ᵥ runCall tag count state ::ᵥ state ::ᵥ nil)
 have hv : List.Vector.ofFn (fun _ : Fin 1 =>
  (count ::ᵥ runCall tag count state ::ᵥ state ::ᵥ nil).get (1 : Fin 3)) =
  runCall tag count state ::ᵥ nil := by
  apply List.Vector.ext
  intro i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => exact Fin.elim0 i
 rw [hv] at hc
 exact ⟨Logic.trans _ _ _ hr hc⟩

theorem substRun {m n : Nat} (sub : Fin m → Term n) tag (count state : Term m) :
 substitute sub (runCall tag count state) = runCall tag (substitute sub count) (substitute sub state) := by
 simp only [runCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.IterationEquationsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.IterationEquationsProof
