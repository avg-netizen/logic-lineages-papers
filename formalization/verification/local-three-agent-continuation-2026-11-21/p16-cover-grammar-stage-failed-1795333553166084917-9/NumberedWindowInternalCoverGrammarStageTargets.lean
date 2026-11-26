module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverGrammarStageTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowCoverAlgorithm (leaves lambdas ordinary numbered cells grammar)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverAuxApplicationsTargets (auxApplications binary reorder)
open NumberedWindowInternalFactoredCoverTargets (GrammarOptionCalibrated)

def originalPrefix (H K : List Nat) (maxNumeral : Nat) (ts args : List Nat) : List Nat :=
  leaves K (List.range (maxNumeral+1)) ++ lambdas K ts ++ ordinary H args ++
    numbered H K (List.range (maxNumeral+1)) args

def LayerPartsCalibrated (prefix : Program 5) (nextArgs : Program 2) : Prop :=
  (∀ H K maxNumeral ts args,
    evaluate prefix (numbersNumber H ::ᵥ numbersNumber K ::ᵥ maxNumeral ::ᵥ
      numbersNumber ts ::ᵥ numbersNumber args ::ᵥ nil) = numbersNumber (originalPrefix H K maxNumeral ts args)) ∧
  (∀ ts args, evaluate nextArgs (numbersNumber ts ::ᵥ numbersNumber args ::ᵥ nil) = numbersNumber (cells ts args))

def termsBefore : Program 5 := reorder InternalUnpair.left ![1]
def argsBefore : Program 5 := reorder InternalUnpair.right ![1]

def prefixAt (prefix : Program 5) : Program 5 :=
  .composition prefix ![.projection 2,.projection 3,.projection 4,termsBefore,argsBefore]

def applicationsAt : Program 5 := binary auxApplications (.projection 3) termsBefore

def termsAtStep (prefix : Program 5) : Program 5 := binary append (prefixAt prefix) applicationsAt

def grammarStep (prefix : Program 5) (nextArgs : Program 2) : Program 5 :=
  binary InternalPairing.pairing (termsAtStep prefix) (binary nextArgs termsBefore argsBefore)

def initialLayer : Program 3 := literal 3 (Nat.pair (numbersNumber []) (numbersNumber [0]))

/-- Depth is the recursive input. Both original lists of one previous stage
are stored together under `Nat.pair`, with fixed H, K and numeral bound. -/
def grammarStage (prefix : Program 5) (nextArgs : Program 2) : Program 4 :=
  .recursion initialLayer (grammarStep prefix nextArgs)

def grammarTerms (prefix : Program 5) (nextArgs : Program 2) : Program 4 :=
  .composition InternalUnpair.left (fun _ : Fin 1 => grammarStage prefix nextArgs)

/-- Call tape [heads, types, actual encoded (depth, maxNumeral)]. -/
def stageGenerator (prefix : Program 5) (nextArgs : Program 2) : Program 3 :=
  .composition .succ (fun _ : Fin 1 =>
    .composition (grammarTerms prefix nextArgs)
      ![reorder InternalUnpair.left ![2],.projection 0,.projection 1,reorder InternalUnpair.right ![2] ])

abbrev termsGraph {α : Type} (prefix : Program 5) (nextArgs : Program 2)
    (out depth H K maxNumeral : OTerm α) := programGraph (grammarTerms prefix nextArgs) out ![depth,H,K,maxNumeral]

def ExactGrammarStageValue : Prop := ∀ (prefix : Program 5) (nextArgs : Program 2),
  LayerPartsCalibrated prefix nextArgs →
  ∀ (H K : List Nat) (maxNumeral depth : Nat),
    let p := grammar H K maxNumeral depth
    evaluate (grammarStage prefix nextArgs) (depth ::ᵥ numbersNumber H ::ᵥ numbersNumber K ::ᵥ maxNumeral ::ᵥ nil) =
      Nat.pair (numbersNumber p.1) (numbersNumber p.2)

def ExactSelectedGrammarStage : Prop := ∃ (prefix : Program 5) (nextArgs : Program 2),
  LayerPartsCalibrated prefix nextArgs ∧ GrammarOptionCalibrated (stageGenerator prefix nextArgs)

/-- True predecessor and successor term-list reports are from the same
physical stage program at exactly the same heads, types and numeral bound. -/
def ExactOpenGrammarStageAuxMember : Prop := ∀ (prefix : Program 5) (nextArgs : Program 2)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (prev out depth H K maxNumeral dom cod fn arg : OTerm α),
  Nonempty (Derivation body Γ (termsGraph prefix nextArgs prev depth H K maxNumeral)) →
  Nonempty (Derivation body Γ (termsGraph prefix nextArgs out (suc depth) H K maxNumeral)) →
  Nonempty (Derivation body Γ (memberGraph K dom)) →
  Nonempty (Derivation body Γ (memberGraph K cod)) →
  Nonempty (Derivation body Γ (memberGraph prev fn)) →
  Nonempty (Derivation body Γ (memberGraph prev arg)) →
  Nonempty (Derivation body Γ (memberGraph out (auxiliaryTerm dom cod fn arg)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverGrammarStageTargets
