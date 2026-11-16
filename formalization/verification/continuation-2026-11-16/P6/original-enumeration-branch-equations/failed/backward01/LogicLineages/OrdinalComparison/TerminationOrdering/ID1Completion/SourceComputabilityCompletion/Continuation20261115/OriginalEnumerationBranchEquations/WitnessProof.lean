module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.WitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.WitnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof hiding OTerm
open InternalRecursionClosureSyntaxProof
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open SourceComputabilityFormulaSupportProof (numeral)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def fields (n : Nat) (out param vb f ts hs ls tb a c prior opened : OTerm alpha) : Formula alpha :=
  graph2 InternalPairing.pairing a vb f ⊓
    graph2 InternalPairing.pairing c (suc vb) f ⊓
    graph2 (OriginalEnumerationRecursion.enumeration n) prior a param ⊓
    graph2 (OriginalEnumerationRecursion.enumeration n) opened c param ⊓
    programGraph (OriginalEnumerationConstructorLayer.layer n) out ![ts,hs,ls,tb,vb,prior,opened]

def matrix (n : Nat) (out param vb f ts hs ls tb : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
  fields n (out.relabel Sum.inl) (param.relabel Sum.inl) (vb.relabel Sum.inl) (f.relabel Sum.inl)
    (ts.relabel Sum.inl) (hs.relabel Sum.inl) (ls.relabel Sum.inl) (tb.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))

theorem fieldsSubst {beta : Type} (n : Nat)
    (out param vb f ts hs ls tb a c prior opened : OTerm alpha) (sub : alpha → OTerm beta) :
    (fields n out param vb f ts hs ls tb a c prior opened).subst (fun a => emb (sub a)) =
      fields n (out.subst sub) (param.subst sub) (vb.subst sub) (f.subst sub) (ts.subst sub) (hs.subst sub)
        (ls.subst sub) (tb.subst sub) (a.subst sub) (c.subst sub) (prior.subst sub) (opened.subst sub) := by
  simp only [fields,conjunctionSubst,graph2,InternalComputabilityApplicationSyntaxProof.programSubst,
    consTermSubst,emptySubst,eqnSubst,sucSubst,numeral,zSubst]
  have hxs : (fun i : Fin 7 => (![ts,hs,ls,tb,vb,prior,opened] i).subst sub) =
      ![ts.subst sub,hs.subst sub,ls.subst sub,tb.subst sub,vb.subst sub,prior.subst sub,opened.subst sub] := by
    funext i
    fin_cases i <;> rfl
  rw [hxs]

theorem matrixWitness (n : Nat) (out param vb f ts hs ls tb : OTerm alpha) (ys : Fin 4 → OTerm alpha) :
    (matrix n out param vb f ts hs ls tb).subst (Sum.elim Term.var (fun i => emb (ys i))) =
      fields n out param vb f ts hs ls tb (ys 0) (ys 1) (ys 2) (ys 3) := by
  have he : Sum.elim Term.var (fun i => emb (ys i)) =
      (fun a => emb (Sum.elim Term.var ys a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he,fieldsSubst]
  simp only [InternalRecursionGraphSyntaxProof.witnessLift,Term.subst,Sum.elim_inr]

theorem successorSubst {beta : Type} (n : Nat) (out param vb f ts hs ls tb : OTerm alpha)
    (sub : alpha → OTerm beta) :
    (Targets.successorOutput n out param vb f ts hs ls tb).subst (fun a => emb (sub a)) =
      Targets.successorOutput n (out.subst sub) (param.subst sub) (vb.subst sub) (f.subst sub)
        (ts.subst sub) (hs.subst sub) (ls.subst sub) (tb.subst sub) := by
  change (InternalFiniteBlocks.block (matrix n out param vb f ts hs ls tb)).subst (fun a => emb (sub a)) =
    InternalFiniteBlocks.block (matrix n (out.subst sub) (param.subst sub) (vb.subst sub) (f.subst sub)
      (ts.subst sub) (hs.subst sub) (ls.subst sub) (tb.subst sub))
  unfold matrix
  rw [OriginalContextInsertionSyntaxProof.blockSubst,liftedEmbedding,fieldsSubst]
  simp only [InternalRecursionGraphSyntaxProof.liftSubst,Term.subst,Sum.elim_inr]

theorem successorRename {beta : Type} (n : Nat) (out param vb f ts hs ls tb : OTerm alpha) (j : alpha → beta) :
    (Targets.successorOutput n out param vb f ts hs ls tb).relabel j =
      Targets.successorOutput n (out.relabel j) (param.relabel j) (vb.relabel j) (f.relabel j)
        (ts.relabel j) (hs.relabel j) (ls.relabel j) (tb.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Targets.successorOutput n out param vb f ts hs ls tb).subst (fun a => emb (.var (j a))) = _
  rw [successorSubst]
  simp only [← termRelabelAsSubst]

theorem introduce (n : Nat) (out param vb f ts hs ls tb : OTerm alpha) (ys : Fin 4 → OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields n out param vb f ts hs ls tb (ys 0) (ys 1) (ys 2) (ys 3)))) :
    Nonempty (Derivation body Delta (Targets.successorOutput n out param vb f ts hs ls tb)) := by
  change Nonempty (Derivation body Delta (InternalFiniteBlocks.block (matrix n out param vb f ts hs ls tb)))
  apply InternalFiniteBlocksProof.introduction body alpha 4 Delta _ (fun i => emb (ys i))
  rw [matrixWitness]
  exact hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.WitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.WitnessProof
