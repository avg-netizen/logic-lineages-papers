module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternal
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal original pair/cons graphs. These are implementation frames and
states, not alternative encodings of source terms or contexts. -/
def FrameGraph {alpha : Type} (frame raw parameter : OTerm alpha) : Formula alpha :=
  graph2 InternalPairing.pairing frame raw parameter

def StateGraph {alpha : Type} (state status work : OTerm alpha) : Formula alpha :=
  graph2 InternalPairing.pairing state status work

def WorkCons {alpha : Type} (work frame rest : OTerm alpha) : Formula alpha :=
  graph2 InternalListCodec.consCode work frame rest

/-- A single CONNECTED live visit. The very same raw value and parameter are
inside the first frame, and the very same remaining work is its list tail. -/
def StateFrame {alpha : Type}
    (state work frame raw parameter rest : OTerm alpha) : Formula alpha :=
  StateGraph state (numeral 1) work ⊓
    (WorkCons work frame rest ⊓ FrameGraph frame raw parameter)

/-- Live and genuinely nonempty, stated using the actual machine selectors.
No frame, list decomposition, raw value or parameter witness is supplied. -/
def LiveWork {alpha : Type} (state : OTerm alpha) : Formula alpha :=
  graph1 status (numeral 1) state ⊓
    (graph1 work OrdinaryArithmetic.zeroTerm state).not

/-- The internally opened constructor graphs retain every ACTUAL selector.
In particular, all later leaf calls use these same raw/parameter terms. -/
def OpenedWork {alpha : Type}
    (state workCode frame raw parameter restCode : OTerm alpha) : Formula alpha :=
  StateFrame state workCode frame raw parameter restCode ⊓
    (graph1 work workCode state ⊓
      (graph1 currentFrame frame state ⊓
        (graph1 currentRaw raw state ⊓
          (graph1 currentParameter parameter state ⊓ graph1 rest restCode state))))

/-- Exact original root-leaf factors. Type and tag witnesses are quantified
INTERNALLY and come from the original raw selectors. Source and target both
accept exactly one; membership is required only at literal application tag
two. There is no hereditary, source-body-validity or calibration premise. -/
def NodeFactors {alpha : Type} (oldSource oldTarget member : Program 2)
    (raw parameter : OTerm alpha) : Formula alpha :=
  graph2 oldSource (numeral 1) raw parameter ⊓
    (graph2 oldTarget (numeral 1) raw parameter ⊓
      InternalFiniteBlocks.block (k := 2)
        (graph1 InternalUnpair.left (.var (.inr (0 : Fin 2))) (raw.relabel Sum.inl) ⊓
          (graph1 OriginalLambdaConstructor.tag (.var (.inr (1 : Fin 2)))
              (raw.relabel Sum.inl) ⊓
            (equal (.var (.inr (1 : Fin 2))) (numeral 2)).imp
              (graph2 member (numeral 1) (.var (.inr (0 : Fin 2)))
                (parameter.relabel Sum.inl)))))

/-- One exact pushed frame at the unchanged work suffix. Its frame and list
codes are internal existential witnesses built from original pair and cons. -/
def PushedFrame {alpha : Type}
    (out raw parameter rest : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 2)
    (StateFrame (out.relabel Sum.inl) (.var (.inr (0 : Fin 2)))
      (.var (.inr (1 : Fin 2))) (raw.relabel Sum.inl)
      (parameter.relabel Sum.inl) (rest.relabel Sum.inl))

/-- Function is visited first, argument second, then the SAME remaining
work. Both children retain the SAME parameter from the original frame. -/
def PushedApplication {alpha : Type}
    (out function argument parameter rest : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 4)
    (StateGraph (out.relabel Sum.inl) (numeral 1) (.var (.inr (0 : Fin 4))) ⊓
      (WorkCons (.var (.inr (0 : Fin 4))) (.var (.inr (2 : Fin 4)))
          (.var (.inr (1 : Fin 4))) ⊓
        (FrameGraph (.var (.inr (2 : Fin 4))) (function.relabel Sum.inl)
            (parameter.relabel Sum.inl) ⊓
          (WorkCons (.var (.inr (1 : Fin 4))) (.var (.inr (3 : Fin 4)))
              (rest.relabel Sum.inl) ⊓
            FrameGraph (.var (.inr (3 : Fin 4))) (argument.relabel Sum.inl)
              (parameter.relabel Sum.inl)))))

/-- Actual typed child selectors of the unchanged machine, not externally
chosen children or a semantic decomposition of a decoded application. -/
def ApplicationResult {alpha : Type}
    (state out parameter rest : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 2)
    (graph1 currentFunction (.var (.inr (0 : Fin 2))) (state.relabel Sum.inl) ⊓
      (graph1 currentArgument (.var (.inr (1 : Fin 2))) (state.relabel Sum.inl) ⊓
        PushedApplication (out.relabel Sum.inl) (.var (.inr (0 : Fin 2)))
          (.var (.inr (1 : Fin 2))) (parameter.relabel Sum.inl)
          (rest.relabel Sum.inl)))

/-- The domain comes from the ACTUAL original raw payload. The parameter is
opened internally into context and encoded Gamma; only Gamma is extended by
that domain using the original cons. The outer context remains unchanged. -/
def ExtendedParameter {alpha : Type}
    (raw parameter bodyParameter : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 4)
    (graph1 OriginalLambdaConstructor.domain (.var (.inr (0 : Fin 4)))
        (raw.relabel Sum.inl) ⊓
      (graph2 InternalPairing.pairing (parameter.relabel Sum.inl)
          (.var (.inr (1 : Fin 4))) (.var (.inr (2 : Fin 4))) ⊓
        (graph2 InternalListCodec.consCode (.var (.inr (3 : Fin 4)))
            (.var (.inr (0 : Fin 4))) (.var (.inr (2 : Fin 4))) ⊓
          graph2 InternalPairing.pairing (bodyParameter.relabel Sum.inl)
            (.var (.inr (1 : Fin 4))) (.var (.inr (3 : Fin 4))))))

/-- The actual body selector supplies the repacked body with the original
outer-type codomain. The newly constructed parameter is ALSO the actual
childParameter selector; its context/Gamma witnesses are not hypotheses. -/
def LambdaResult {alpha : Type}
    (state out raw parameter rest : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 2)
    (graph1 currentBody (.var (.inr (0 : Fin 2))) (state.relabel Sum.inl) ⊓
      (ExtendedParameter (raw.relabel Sum.inl) (parameter.relabel Sum.inl)
          (.var (.inr (1 : Fin 2))) ⊓
        (graph1 childParameter (.var (.inr (1 : Fin 2))) (state.relabel Sum.inl) ⊓
          PushedFrame (out.relabel Sum.inl) (.var (.inr (0 : Fin 2)))
            (.var (.inr (1 : Fin 2))) (rest.relabel Sum.inl))))

/-- Internal pair/list totality supplies every witness of the actual live
state. The continuation carries renamed assumptions, as in the existing
original context-extension supplier. No existential witness is an oracle. -/
def LiveWorkOpening : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Gamma : List (Formula alpha))
    (state : OTerm alpha) (psi : Formula alpha),
  Nonempty (Derivation body Gamma (LiveWork state)) →
  (∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)),
    (∀ h ∈ Gamma, h.relabel j ∈ Delta) →
    ∀ workCode frame raw parameter restCode : OTerm beta,
    Nonempty (Derivation body Delta
      (OpenedWork (state.relabel j) workCode frame raw parameter restCode)) →
    Nonempty (Derivation body Delta (psi.relabel j))) →
  Nonempty (Derivation body Gamma psi)

/- INTERNAL ONE-STEP PACKET ONLY. All formulas refer to the unchanged
OriginalHereditaryValidity AST and original pair/list/term selectors.
No evaluate equality, native recurrence, typed source acceptance, successful
bounded run, body validity or final source Program is assumed or concluded.

Internal bounded-run recurrence, stack append/fuel accounting, hereditary
bottom-parameter invariance, guard-to-SAME-final-source transport, original
lambda-body validity, and complete final Package retention remain pending. -/

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternal
