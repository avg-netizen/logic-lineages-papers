module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.GenericObservationsSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph2)
open InternalTagArithmeticSyntaxProof (emb eqn eqnSubst zSubst sucSubst)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalRecursionClosureSyntaxProof InternalAdditionLawsProof InternalQuotientComparisonSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph
/-- Proof-only original ordered twelve-conjunct shape, with opaque programs/formulas. -/
def observations {alpha : Type} (p : Fin 8 → Program 2) (pair : Program 2)
    (seed param candidate : OTerm alpha) (xs : Fin 9 → OTerm alpha)
    (fields depth : Formula alpha) : Formula alpha :=
  graph2 (p 0) (xs 1) seed param ⊓ graph2 (p 1) (xs 2) seed param ⊓
  graph2 (p 2) (xs 3) seed param ⊓ graph2 (p 3) (xs 4) seed param ⊓
  graph2 (p 4) (xs 5) seed param ⊓ graph2 (p 5) (xs 6) seed param ⊓
  graph2 (p 6) (xs 7) seed param ⊓ graph2 (p 7) (xs 8) seed param ⊓
  (eqn (xs 8) (numeral 0)).not ⊓ graph2 pair candidate (xs 1) (xs 0) ⊓ fields ⊓ depth

theorem subst {alpha beta : Type} (p : Fin 8 → Program 2) (pair : Program 2)
    (seed param candidate : OTerm alpha) (xs : Fin 9 → OTerm alpha) (ts : alpha → OTerm beta)
    (fields depth : Formula alpha) (fields' depth' : Formula beta)
    (hf : fields.subst (fun a => emb (ts a)) = fields')
    (hd : depth.subst (fun a => emb (ts a)) = depth') :
    (observations p pair seed param candidate xs fields depth).subst (fun a => emb (ts a)) =
      observations p pair (seed.subst ts) (param.subst ts) (candidate.subst ts)
        (fun i => (xs i).subst ts) fields' depth' := by
  unfold observations
  simp only [conjunctionSubst,notSubst,eqnSubst,
    InternalApplicationValidityStackAppendSyntaxProof.graph2Subst,hf,hd,
    SourceComputabilityFormulaSupportProof.numeral,zSubst,sucSubst]
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.GenericObservationsSyntaxProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.GenericObservationsSyntaxProof
