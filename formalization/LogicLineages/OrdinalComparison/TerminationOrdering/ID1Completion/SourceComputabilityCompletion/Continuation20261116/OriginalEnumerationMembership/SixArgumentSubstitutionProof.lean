module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public import Mathlib.Tactic.FinCases
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.SixArgumentSubstitutionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (emb zSubst sucSubst)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph
/-- Generic proof-only boundary: the program remains an arbitrary parameter,
so vector substitution is proved without elaborating the concrete Fields AST. -/
theorem acceptedSubst {alpha beta : Type} (p : Program 6)
    (a b c d e f : OTerm alpha) (ts : alpha → OTerm beta) :
    (programGraph p (numeral 1) ![a,b,c,d,e,f]).subst (fun x => emb (ts x)) =
      programGraph p (numeral 1) ![a.subst ts,b.subst ts,c.subst ts,d.subst ts,e.subst ts,f.subst ts] := by
  rw [InternalRawListRecursionSyntaxProof.programSubst]
  simp only [SourceComputabilityFormulaSupportProof.numeral,zSubst,sucSubst]
  have hx : (fun i => ((![a,b,c,d,e,f] : Fin 6 → OTerm alpha) i).subst ts) =
      ![a.subst ts,b.subst ts,c.subst ts,d.subst ts,e.subst ts,f.subst ts] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.SixArgumentSubstitutionProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.SixArgumentSubstitutionProof
