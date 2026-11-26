module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.ValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.WitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.BackwardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def listTail : Program 4 := .composition InternalListCodec.consCode ![.projection 1,InternalAcceptance.constantZero 4]
def listPair : Program 4 := .composition InternalListCodec.consCode ![.projection 0,listTail]
def valueTail : Program 4 := .composition InternalListCodec.consCode ![.projection 3,InternalAcceptance.constantZero 4]
def valuePair : Program 4 := .composition InternalListCodec.consCode ![.projection 2,valueTail]
def queries : Fin 4 → Program 4 := ![listTail,listPair,valueTail,valuePair]

theorem fieldsRename {beta : Type} (n : Nat)
    (out param vb f ts hs ls tb a c prior opened : OTerm alpha) (j : alpha → beta) :
    (WitnessProof.fields n out param vb f ts hs ls tb a c prior opened).relabel j =
      WitnessProof.fields n (out.relabel j) (param.relabel j) (vb.relabel j) (f.relabel j)
        (ts.relabel j) (hs.relabel j) (ls.relabel j) (tb.relabel j)
        (a.relabel j) (c.relabel j) (prior.relabel j) (opened.relabel j) := by
  rw [InternalSourceIntroductionSyntaxProof.formulaRelabelAsSubst]
  change (WitnessProof.fields n out param vb f ts hs ls tb a c prior opened).subst
    (fun a => InternalTagArithmeticSyntaxProof.emb (.var (j a))) = _
  rw [WitnessProof.fieldsSubst]
  simp only [← InternalSourceIntroductionSyntaxProof.termRelabelAsSubst]

theorem atFields (n : Nat) (node param vb f ts hs ls tb p2 p3 out a c prior opened : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node vb (suc f))))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ts p2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p2 hs p3)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p3 ls tb)))
    (hw : Nonempty (Derivation body Delta (WitnessProof.fields n out param vb f ts hs ls tb a c prior opened))) :
    Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) out node param)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases queries ![a,c,prior,opened] _
  intro beta j ys Theta hj hq
  have hxs : (fun i : Fin 4 => (![a,c,prior,opened] i).relabel j) =
      ![a.relabel j,c.relabel j,prior.relabel j,opened.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hxs] at hq
  rw [graph2Rename]
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,sucRelabel] at hnj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [graph2Rename,sucRelabel] at hpj
  have h2j := InternalGraphCompositionFunctionalityProof.renameInto h2 j Theta hj
  simp only [graph2Rename,sucRelabel] at h2j
  have h3j := InternalGraphCompositionFunctionalityProof.renameInto h3 j Theta hj
  simp only [graph2Rename,sucRelabel] at h3j
  have hwj := InternalGraphCompositionFunctionalityProof.renameInto hw j Theta hj
  rw [fieldsRename] at hwj
  have ha := andLeft (andLeft (andLeft (andLeft hwj)))
  have hc := andRight (andLeft (andLeft (andLeft hwj)))
  have hea := andRight (andLeft (andLeft hwj))
  have hec := andRight (andLeft hwj)
  have hl := andRight hwj
  let xs : Fin 4 → OTerm beta := ![a.relabel j,c.relabel j,prior.relabel j,opened.relabel j]
  have ht := binaryRecover InternalListCodec.consCode (.projection 1) (InternalAcceptance.constantZero 4)
    (ys 0) (c.relabel j) z xs (hq 0) (projectionValue 1 xs)
    (InternalAcceptanceConjunctionProof.constantZeroValue xs)
  have hd := binaryRecover InternalListCodec.consCode (.projection 0) listTail
    (ys 1) (a.relabel j) (ys 0) xs (hq 1) (projectionValue 0 xs) (hq 0)
  have hr := binaryRecover InternalListCodec.consCode (.projection 3) (InternalAcceptance.constantZero 4)
    (ys 2) (opened.relabel j) z xs (hq 2) (projectionValue 3 xs)
    (InternalAcceptanceConjunctionProof.constantZeroValue xs)
  have hv := binaryRecover InternalListCodec.consCode (.projection 2) valueTail
    (ys 3) (prior.relabel j) (ys 2) xs (hq 3) (projectionValue 2 xs) (hq 2)
  exact ValueProof.atValues n (node.relabel j) (param.relabel j) (vb.relabel j) (f.relabel j)
    (ts.relabel j) (hs.relabel j) (ls.relabel j) (tb.relabel j) (p2.relabel j) (p3.relabel j)
    (a.relabel j) (c.relabel j) (prior.relabel j) (opened.relabel j) (ys 1) (ys 0) (ys 3) (ys 2)
    (out.relabel j) hnj hpj h2j h3j ha hc hea hec ht hd hr hv hl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.BackwardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.BackwardProof
