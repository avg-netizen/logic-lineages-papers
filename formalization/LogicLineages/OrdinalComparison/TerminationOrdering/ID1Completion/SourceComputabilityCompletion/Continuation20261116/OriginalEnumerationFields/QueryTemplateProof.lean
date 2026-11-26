module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.QueryTemplateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

/-- Finite proof-only composition template; no recursion, truth oracle or new primitive. -/
inductive Template where
  | input
  | node (arity : Nat) (program : Program arity) (children : Fin arity → Template)

def instantiate {k : Nat} (query : Program k) : Template → Program k
  | .input => query
  | .node _ p ts => .composition p (fun i => instantiate query (ts i))

/-- Changing only the input implementation preserves every original graph result
provided both actual query graphs have the same witnessed value. -/
theorem forward (t : Template) : ∀ {k l : Nat} (p : Program k) (q : Program l)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (xs : Fin k → OTerm alpha) (ys : Fin l → OTerm alpha) (raw out : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph p raw xs)) →
  Nonempty (Derivation body Delta (programGraph q raw ys)) →
  Nonempty (Derivation body Delta (programGraph (instantiate p t) out xs)) →
  Nonempty (Derivation body Delta (programGraph (instantiate q t) out ys)) := by
  induction t with
  | input =>
    intro k l p q body alpha Delta xs ys raw out hp hq ho
    obtain ⟨he⟩ := valueUnique p out raw xs ho hp
    exact outputTransport q raw out ys ⟨symm he⟩ hq
  | node arity f ts ih =>
    intro k l p q body alpha Delta xs ys raw out hp hq ho
    apply programCompositionCases f (fun i => instantiate p (ts i)) out xs _ ho
    intro beta j zs Theta hj hf ht
    rw [programRename]
    have hpj := renameInto hp j Theta hj
    have hqj := renameInto hq j Theta hj
    rw [programRename] at hpj hqj
    exact compositionValue f (fun i => instantiate q (ts i)) (out.relabel j)
      (fun i => (ys i).relabel j) zs hf
      (fun i => ih i p q body beta Theta (fun i => (xs i).relabel j)
        (fun i => (ys i).relabel j) (raw.relabel j) (zs i) hpj hqj (ht i))

def zero : Template := .node 0 .zero Fin.elim0
def suc (t : Template) : Template := .node 1 .succ (fun _ => t)
def constant : Nat → Template
  | 0 => zero
  | n+1 => suc (constant n)
def left (t : Template) : Template := .node 1 InternalUnpair.left (fun _ => t)
def right (t : Template) : Template := .node 1 InternalUnpair.right (fun _ => t)
def same (a b : Template) : Template := .node 2 InternalEqualityTest.equalityTest ![a,b]
def branch (a b c : Template) : Template := .node 3
  LogicLineages.ComputabilityKnowledge.GorbowPRInternalControl.conditional
  (Fin.cons a (Fin.cons b (Fin.cons c Fin.elim0)))

theorem instantiateConstant {k : Nat} (p : Program k) (n : Nat) :
    instantiate p (constant n) = OriginalRawSyntaxTransport.constant k n := by
  induction n with
  | zero =>
    simp only [constant,zero,instantiate,OriginalRawSyntaxTransport.constant,InternalAcceptance.constantZero]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih => simp only [constant,suc,instantiate,ih]; rfl

theorem instantiateLeft {k : Nat} (p : Program k) (t : Template) :
    instantiate p (left t) = leftOf (instantiate p t) := rfl

theorem instantiateRight {k : Nat} (p : Program k) (t : Template) :
    instantiate p (right t) = rightOf (instantiate p t) := rfl

theorem instantiateSame {k : Nat} (p : Program k) (a b : Template) :
    instantiate p (same a b) = OriginalRawSyntaxTransport.sameOf (instantiate p a) (instantiate p b) := by
  simp only [same,instantiate,OriginalRawSyntaxTransport.sameOf,InternalApplicationStepPeel.same]
  congr 1
  funext i
  fin_cases i <;> simp [Fin.cons]

theorem instantiateBranch {k : Nat} (p : Program k) (a b c : Template) :
    instantiate p (branch a b c) = InternalAcceptance.branch
      (instantiate p a) (instantiate p b) (instantiate p c) := by
  simp only [branch,instantiate,InternalAcceptance.branch]
  congr 1
  funext i
  fin_cases i <;> rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.QueryTemplateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.QueryTemplateProof
