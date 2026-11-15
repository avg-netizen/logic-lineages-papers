module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.WitnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding OTerm
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalRawListRecursionSyntaxProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open Targets
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem fieldsSubst {beta : Type} (n : Nat)
    (labels heads types bases tuples extras code k encodedHead rawHead t b ts e : OTerm alpha)
    (sub : alpha → OTerm beta) :
    (fields n labels heads types bases tuples extras code k encodedHead rawHead t b ts e).subst (fun a => emb (sub a)) =
    fields n (labels.subst sub) (heads.subst sub) (types.subst sub) (bases.subst sub)
      (tuples.subst sub) (extras.subst sub) (code.subst sub) (k.subst sub) (encodedHead.subst sub)
      (rawHead.subst sub) (t.subst sub) (b.subst sub) (ts.subst sub) (e.subst sub) := by
  simp only [fields,conjunctionSubst,graph1,graph2,InternalComputabilityApplicationSyntaxProof.programSubst,
    numeral,zSubst,sucSubst,consTermSubst,emptySubst]
  rfl

@[simp] theorem fieldsRename {beta : Type} (n : Nat)
    (labels heads types bases tuples extras code k encodedHead rawHead t b ts e : OTerm alpha)
    (j : alpha → beta) :
    (fields n labels heads types bases tuples extras code k encodedHead rawHead t b ts e).relabel j =
    fields n (labels.relabel j) (heads.relabel j) (types.relabel j) (bases.relabel j)
      (tuples.relabel j) (extras.relabel j) (code.relabel j) (k.relabel j) (encodedHead.relabel j)
      (rawHead.relabel j) (t.relabel j) (b.relabel j) (ts.relabel j) (e.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fields n labels heads types bases tuples extras code k encodedHead rawHead t b ts e).subst
    (fun a => emb (.var (j a))) = _
  rw [fieldsSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness (n : Nat)
    (labels heads types bases tuples extras code k encodedHead rawHead t b ts e : OTerm alpha) :
    (witnessMatrix n labels heads types bases tuples extras code).subst
      (Sum.elim Term.var (fun i => emb (![k,encodedHead,rawHead,t,b,ts,e] i))) =
    fields n labels heads types bases tuples extras code k encodedHead rawHead t b ts e := by
  have he : Sum.elim Term.var (fun i => emb (![k,encodedHead,rawHead,t,b,ts,e] i)) =
      (fun a => emb (Sum.elim Term.var ![k,encodedHead,rawHead,t,b,ts,e] a)) := by
    funext a
    cases a <;> rfl
  unfold witnessMatrix
  rw [he,fieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem introduce (n : Nat)
    (labels heads types bases tuples extras code k encodedHead rawHead t b ts e : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields n labels heads types bases tuples extras code k encodedHead rawHead t b ts e))) :
    Nonempty (Derivation body Delta (InternalFiniteBlocks.block (witnessMatrix n labels heads types bases tuples extras code))) := by
  apply InternalFiniteBlocksProof.introduction body alpha 7 Delta _ (fun i => emb (![k,encodedHead,rawHead,t,b,ts,e] i))
  rw [matrixWitness]
  exact hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.WitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.WitnessProof
