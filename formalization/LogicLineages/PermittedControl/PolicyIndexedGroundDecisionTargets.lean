module
public import LogicLineages.PermittedControl.PolicyIndexedGroundDriverTargets

@[expose] public section
namespace LogicLineages.PermittedControl.PolicyIndexedGroundDriver
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax Source.ForwardTranslation
open GroundComparison (Relation Canonical)
open StandardControlCurrent.PolicyIndexedShape (Implements)
open Nat.Partrec (Code)

/-- For each relation, one primitive-recursive transformation of a supplied
policy-program index into a decider-program index. The transformation is
chosen before the policy index and policy, and acts on coded original terms. -/
def IndexedGroundDecidable (ctrl : Nat → Nat) : Prop :=
  ∀ rel : Relation, ∃ compile : Code → Code, Primrec compile ∧
    ∀ (e : Code) (p : Policy), Implements e p →
      ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
      ∀ (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ), ∃ ans : Bool,
        Code.eval (compile e) (Encodable.encode (Γ.length,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)) =
          Part.some (Encodable.encode ans) ∧ (ans = true ↔ Canonical ctrl p rel a b)

def IndexedGroundFromSourceAndQuery : Prop :=
  ∀ src : IndexedSource, Partrec src → SourceExact src →
    ∀ query : Query, GroundComparisonAssembly.QueryInterface query →
      Computable (fun x : TermInput => query x.1 x.2.1 x.2.2) →
      IndexedGroundDecidable factorialControl ∧ ∀ b : Nat, IndexedGroundDecidable (nearControl b)

end LogicLineages.PermittedControl.PolicyIndexedGroundDriver
