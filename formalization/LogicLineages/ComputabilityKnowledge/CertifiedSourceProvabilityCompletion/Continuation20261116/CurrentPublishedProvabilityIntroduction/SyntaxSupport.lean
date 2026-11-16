module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeInputs
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.TemplateSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.SyntaxSupport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowSubstitution GorbowFormulaSubstitution
abbrev closed {n : Nat} (u : Term 0) : Term n := renameTerm Fin.elim0 u

theorem substituteClosed {m n : Nat} (s : Fin m → Term n) (u : Term 0) :
 substitute s (closed (n := m) u) = closed (n := n) u := by
 unfold closed renameTerm
 rw [substitute_composition]
 congr 1
 funext i
 exact Fin.elim0 i

theorem renameClosed {m n : Nat} (r : Fin m → Fin n) (u : Term 0) :
 renameTerm r (closed (n := m) u) = closed (n := n) u := substituteClosed _ u

theorem closedNumeral (n value : Nat) : closed (n := n) (Term.numeral value) = Term.numeral value :=
 SixSol20261112.Fuel.Logic.substNumeral _ value

theorem callSubstitute {m n arity : Nat} (s : Fin m → Term n) (tag : Nat) (args : List.Vector (Term m) arity) :
 substitute s (call tag args) = call tag (args.map (substitute s)) := by
 change substitute s (CurrentRecursionBaseProgram.openCall (Term.numeral tag) args) = _
 rw [CurrentRecursionStepProgram.TemplateSyntax.openCallSubstitute,SixSol20261112.Fuel.Logic.substNumeral]
 rfl

def checkerBody (tag index : Nat) (u : Term 0) : Formula 2 :=
 .equal (call tag (Term.numeral index ::ᵥ .var 1 ::ᵥ .zero ::ᵥ closed u ::ᵥ .var 0 ::ᵥ nil)) (.succ .zero)
def checkerInner (tag index fuel : Nat) (u : Term 0) : Formula 1 :=
 .equal (call tag (Term.numeral index ::ᵥ Term.numeral fuel ::ᵥ .zero ::ᵥ closed u ::ᵥ .var 0 ::ᵥ nil)) (.succ .zero)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.SyntaxSupport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.SyntaxSupport
