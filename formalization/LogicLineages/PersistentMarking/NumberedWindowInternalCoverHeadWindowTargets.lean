module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedInductionDispatchTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalAuxWindowMemoTargets (IntrinsicWindowCalibrated)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm)
open NumberedWindowInternalCoverFittedInductionDispatchTargets (fittedWindowBase fittedPrograms)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)

def headTag (numbered : Bool) : Nat := if numbered then 5 else 4
def headArity (numbered : Bool) : Nat := if numbered then 5 else 2

abbrev headPrior {α : Type} (b : Bool) (h : OTerm α) (tail : List (OTerm α)) : OTerm α :=
  pairTerm (numeral (headTag b)) (packedBody (h::tail))

abbrev headKey {α : Type} (b : Bool) (h : OTerm α) (tail : List (OTerm α)) : OTerm α :=
  rawCons (numeral (headTag b)) (packedBody (h::tail))

def grammarHeadAt (s : Settings) : Program 1 :=
  .composition scratchMember ![literal 1 (Encodable.encode s.window.2),.projection 0]

def storedHeadInGrammar (s : Settings) : Program 1 :=
  .composition (grammarHeadAt s) (fun _ : Fin 1 => field 0)

def headPositive (s : Settings) (B : Program 2) : Program 2 :=
  branch (normalize (onRaw (storedHeadInGrammar s))) (constantZero 2) B

def headBaseAt (b : Bool) (s : Settings) (B : Program 2) : Program 2 :=
  branch (onRaw (header (headTag b) (headArity b))) B (headPositive s B)

def grammarHeadBase (s : Settings) (B : Program 2) : Program 2 :=
  headBaseAt false s (headBaseAt true s B)

abbrev headFittedWindow (s : Settings) (B : Program 2) (T : Program 1) : Program 3 :=
  strictAuxWindow (fittedWindowBase s (grammarHeadBase s B)) (refitGuard s T)

def ExactCoverHeadBaseAt : Prop :=
  ∀ (b : Bool) (s : Settings) (B : Program 2), IntrinsicWindowCalibrated s B →
    IntrinsicWindowCalibrated s (headBaseAt b s B)

def ExactCoverGrammarHeadBase : Prop :=
  ∀ (s : Settings) (B : Program 2), IntrinsicWindowCalibrated s B →
    IntrinsicWindowCalibrated s (grammarHeadBase s B)

structure HeadKeyReports (b : Bool) (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (h : OTerm α) (tail : List (OTerm α)) : Prop where
  notAux : Nonempty (Derivation body Γ (unary termShape z (headKey b h tail)))
  notTypeLeaf : Nonempty (Derivation body Γ (unary (header 3 1) z (headKey b h tail)))
  notFree : Nonempty (Derivation body Γ (unary (header 0 2) z (headKey b h tail)))
  notBound : Nonempty (Derivation body Γ (unary (header 1 2) z (headKey b h tail)))
  accepted : Nonempty (Derivation body Γ (unary (header (headTag b) (headArity b)) (suc z) (headKey b h tail)))
  fieldHead : Nonempty (Derivation body Γ (unary (field 0) h (headKey b h tail)))
  notOrdinary : b = true → Nonempty (Derivation body Γ (unary (header 4 2) z (headKey b h tail)))

def ExactOpenCoverHeadShape : Prop :=
  ∀ (b : Bool) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (h : OTerm α) (tail : List (OTerm α)), (h::tail).length = headArity b →
    HeadKeyReports b body Γ h tail

def ExactOpenCoverHeadIntrinsic : Prop :=
  ∀ (b : Bool) (s : Settings) (B : Program 2) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx h result : OTerm α) (tail : List (OTerm α)),
    (h::tail).length = headArity b →
    Nonempty (Derivation body Γ (programGraph (fittedWindowBase s (grammarHeadBase s B)) (suc result)
      ![ctx,headKey b h tail])) →
    Nonempty (Derivation body Γ (memberGraph (headsTerm s α) h))

def ExactOpenCoverHeadFittedWindow : Prop :=
  ∀ (b : Bool) (s : Settings) (B : Program 2) (T : Program 1) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (ctx h result : OTerm α) (tail : List (OTerm α)),
    (h::tail).length = headArity b →
    Nonempty (Derivation body Γ (windowGraph (headFittedWindow s B T) ctx result (headKey b h tail))) →
    Nonempty (Derivation body Γ (memberGraph (headsTerm s α) h))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowTargets
