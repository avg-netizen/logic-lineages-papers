module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.InductionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (emb z suc sucSubst zSubst)
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Induction
attribute [local irreducible] programGraph

theorem graphOneSubst {alpha beta : Type} (P : Program 1) (out x : OTerm alpha) (ts : alpha → OTerm beta) :
    (graph1 P out x).subst (fun a => emb (ts a)) = graph1 P (out.subst ts) (x.subst ts) := by
  simp only [graph1,InternalComputabilityApplicationSyntaxProof.programSubst,consTermSubst,emptySubst]
theorem graphTwoSubst {alpha beta : Type} (P : Program 2) (out x y : OTerm alpha) (ts : alpha → OTerm beta) :
    (graph2 P out x y).subst (fun a => emb (ts a)) = graph2 P (out.subst ts) (x.subst ts) (y.subst ts) := by
  simp only [graph2,InternalComputabilityApplicationSyntaxProof.programSubst,consTermSubst,emptySubst]

theorem environmentSubst {alpha beta : Type} (n : Nat)
    (context symbols types window : OTerm alpha) (ts : alpha → OTerm beta) :
    (environment n context symbols types window).subst (fun a => emb (ts a)) = environment n (context.subst ts) (symbols.subst ts) (types.subst ts) (window.subst ts) := by
  simp only [environment,conjunctionSubst,graphOneSubst,graphTwoSubst,numeral,sucSubst,zSubst]
@[simp] theorem environmentRename {alpha beta : Type} (n : Nat)
    (context symbols types window : OTerm alpha) (j : alpha → beta) :
    (environment n context symbols types window).relabel j = environment n (context.relabel j) (symbols.relabel j) (types.relabel j) (window.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (environment n context symbols types window).subst (fun a => emb (.var (j a))) = _
  rw [environmentSubst]
  simp only [← termRelabelAsSubst]

theorem edgeSubst {alpha beta : Type} (n : Nat) (arity : Fin n → Nat)
    (source target node window : OTerm alpha) (ts : alpha → OTerm beta) :
    (edge n arity source target node window).subst (fun a => emb (ts a)) = edge n arity (source.subst ts) (target.subst ts) (node.subst ts) (window.subst ts) := by
  simp only [edge,conjunctionSubst,graphOneSubst,graphTwoSubst,numeral,sucSubst,zSubst]
@[simp] theorem edgeRename {alpha beta : Type} (n : Nat) (arity : Fin n → Nat)
    (source target node window : OTerm alpha) (j : alpha → beta) :
    (edge n arity source target node window).relabel j = edge n arity (source.relabel j) (target.relabel j) (node.relabel j) (window.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (edge n arity source target node window).subst (fun a => emb (.var (j a))) = _
  rw [edgeSubst]
  simp only [← termRelabelAsSubst]

theorem acceptedSubst {alpha beta : Type} (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
    (typ raw gamma context : OTerm alpha) (ts : alpha → OTerm beta) :
    (accepted n arity arguments typ raw gamma context).subst (fun a => emb (ts a)) = accepted n arity arguments (typ.subst ts) (raw.subst ts) (gamma.subst ts) (context.subst ts) := by
  simp only [accepted,OriginalUniverseDecoderTransportSyntaxProof.acceptedSubst]
@[simp] theorem acceptedRename {alpha beta : Type} (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
    (typ raw gamma context : OTerm alpha) (j : alpha → beta) :
    (accepted n arity arguments typ raw gamma context).relabel j = accepted n arity arguments (typ.relabel j) (raw.relabel j) (gamma.relabel j) (context.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (accepted n arity arguments typ raw gamma context).subst (fun a => emb (.var (j a))) = _
  rw [acceptedSubst]
  simp only [← termRelabelAsSubst]

theorem plainSubst {alpha beta : Type} (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
    (typ raw gamma : OTerm alpha) (ts : alpha → OTerm beta) :
    (plain n arity arguments typ raw gamma).subst (fun a => emb (ts a)) = plain n arity arguments (typ.subst ts) (raw.subst ts) (gamma.subst ts) := by
  simp only [plain,OriginalTypedDecoderTransportSyntaxProof.acceptedSubst]
@[simp] theorem plainRename {alpha beta : Type} (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
    (typ raw gamma : OTerm alpha) (j : alpha → beta) :
    (plain n arity arguments typ raw gamma).relabel j = plain n arity arguments (typ.relabel j) (raw.relabel j) (gamma.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (plain n arity arguments typ raw gamma).subst (fun a => emb (.var (j a))) = _
  rw [plainSubst]
  simp only [← termRelabelAsSubst]

theorem rowSubst {alpha beta : Type} (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
    (source typ target gamma context symbols types window node : OTerm alpha) (ts : alpha → OTerm beta) :
    (row n arity arguments source typ target gamma context symbols types window node).subst (fun a => emb (ts a)) = row n arity arguments (source.subst ts) (typ.subst ts) (target.subst ts) (gamma.subst ts) (context.subst ts) (symbols.subst ts) (types.subst ts) (window.subst ts) (node.subst ts) := by
  simp only [row,impSubst,conjunctionSubst,environmentSubst,edgeSubst,acceptedSubst,plainSubst]
@[simp] theorem rowRename {alpha beta : Type} (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
    (source typ target gamma context symbols types window node : OTerm alpha) (j : alpha → beta) :
    (row n arity arguments source typ target gamma context symbols types window node).relabel j = row n arity arguments (source.relabel j) (typ.relabel j) (target.relabel j) (gamma.relabel j) (context.relabel j) (symbols.relabel j) (types.relabel j) (window.relabel j) (node.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row n arity arguments source typ target gamma context symbols types window node).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.InductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.InductionSyntaxProof
