module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafInternalChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildStateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open OriginalHereditaryLambda
open OriginalLambdaGuardLeafInternalProof (combine projectLeft projectRight)
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalControlGraphSupportProof InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalEqualityTestPredecessorProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

abbrev lastPair : Program 4 := pairOf (.projection 2) (.projection 3)
abbrev restPair : Program 4 := pairOf (.projection 1) lastPair
abbrev fullPair : Program 4 := pairOf (.projection 0) restPair

/-- Only a proof-side bundle of the four literal original state selectors. -/
def Fields (state source target certificate parameter : OTerm alpha) : Formula alpha :=
  graph1 stateSource source state ⊓
    (graph1 stateTarget target state ⊓
      (graph1 stateCertificate certificate state ⊓ graph1 stateParameter parameter state))

@[simp] theorem fieldsRename {beta : Type}
    (state source target certificate parameter : OTerm alpha) (j : alpha → beta) :
    (Fields state source target certificate parameter).relabel j =
      Fields (state.relabel j) (source.relabel j) (target.relabel j)
        (certificate.relabel j) (parameter.relabel j) := by
  change (graph1 stateSource source state).relabel j ⊓
    ((graph1 stateTarget target state).relabel j ⊓
      ((graph1 stateCertificate certificate state).relabel j ⊓
        (graph1 stateParameter parameter state).relabel j)) = _
  simp only [graph1Rename]
  rfl

/-- The original nested pairing construction and predecessor inverse recover
all four fields, including on arbitrary malformed original inputs. -/
theorem fieldsAtPairs (state source target certificate parameter payload rest last : OTerm alpha)
    (hl : Nonempty (Derivation body Delta
      (graph4 live state source target certificate parameter)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing last certificate parameter)))
    (hb : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rest target last)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload source rest))) :
    Nonempty (Derivation body Delta (Fields state source target certificate parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons source (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  have hlast := binaryValue InternalPairing.pairing (.projection 2) (.projection 3)
    last certificate parameter xs ha (projectionValue 2 xs) (projectionValue 3 xs)
  have hrest := binaryValue InternalPairing.pairing (.projection 1) lastPair
    rest target last xs hb (projectionValue 1 xs) hlast
  have hfull := binaryValue InternalPairing.pairing (.projection 0) restPair
    payload source rest xs hc (projectionValue 0 xs) hrest
  have hs := unaryValue .succ fullPair (suc payload) payload xs
    (successorValue (Fin.cons payload Fin.elim0)) hfull
  obtain ⟨he⟩ := valueUnique live state (suc payload) xs hl hs
  have hp : Nonempty (Derivation body Delta (graph1 statePayload payload state)) :=
    headTransport statePayload payload (suc payload) state Fin.elim0
      ⟨symm he⟩ (predecessorSuccessor payload)
  have h0 := unaryValue InternalUnpair.left statePayload source payload
    (Fin.cons state Fin.elim0) (pairLeft payload source rest hc) hp
  have hr := unaryValue InternalUnpair.right statePayload rest payload
    (Fin.cons state Fin.elim0) (pairRight payload source rest hc) hp
  have h1 := unaryValue InternalUnpair.left (rightOf statePayload) target rest
    (Fin.cons state Fin.elim0) (pairLeft rest target last hb) hr
  have hh := unaryValue InternalUnpair.right (rightOf statePayload) last rest
    (Fin.cons state Fin.elim0) (pairRight rest target last hb) hr
  have h2 := unaryValue InternalUnpair.left (rightOf (rightOf statePayload)) certificate last
    (Fin.cons state Fin.elim0) (pairLeft last certificate parameter ha) hh
  have h3 := unaryValue InternalUnpair.right (rightOf (rightOf statePayload)) parameter last
    (Fin.cons state Fin.elim0) (pairRight last certificate parameter ha) hh
  exact combine h0 (combine h1 (combine h2 h3))

theorem fieldsAtRest (state source target certificate parameter rest last : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph4 live state source target certificate parameter)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing last certificate parameter)))
    (hb : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rest target last))) :
    Nonempty (Derivation body Delta (Fields state source target certificate parameter)) := by
  apply programCases InternalPairing.pairing (Fin.cons source (Fin.cons rest Fin.elim0)) _
  intro beta j Theta payload hj hc
  rw [fieldsRename]
  have hl' := renameInto hl j Theta hj
  have ha' := renameInto ha j Theta hj
  have hb' := renameInto hb j Theta hj
  simp only [graph4Rename, graph2Rename] at hl' ha' hb'
  simp only [consTermRename, emptyRename] at hc
  exact fieldsAtPairs (state.relabel j) (source.relabel j) (target.relabel j)
    (certificate.relabel j) (parameter.relabel j) payload (rest.relabel j) (last.relabel j)
    hl' ha' hb' hc

theorem fieldsAtLast (state source target certificate parameter last : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph4 live state source target certificate parameter)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing last certificate parameter))) :
    Nonempty (Derivation body Delta (Fields state source target certificate parameter)) := by
  apply programCases InternalPairing.pairing (Fin.cons target (Fin.cons last Fin.elim0)) _
  intro beta j Theta rest hj hb
  rw [fieldsRename]
  have hl' := renameInto hl j Theta hj
  have ha' := renameInto ha j Theta hj
  simp only [graph4Rename, graph2Rename] at hl' ha'
  simp only [consTermRename, emptyRename] at hb
  exact fieldsAtRest (state.relabel j) (source.relabel j) (target.relabel j)
    (certificate.relabel j) (parameter.relabel j) rest (last.relabel j) hl' ha' hb

theorem liveFields (state source target certificate parameter : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph4 live state source target certificate parameter))) :
    Nonempty (Derivation body Delta (Fields state source target certificate parameter)) := by
  apply programCases InternalPairing.pairing (Fin.cons certificate (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta last hj ha
  rw [fieldsRename]
  have hl' := renameInto hl j Theta hj
  simp only [graph4Rename] at hl'
  simp only [consTermRename, emptyRename] at ha
  exact fieldsAtLast (state.relabel j) (source.relabel j) (target.relabel j)
    (certificate.relabel j) (parameter.relabel j) last hl' ha

 theorem fieldsComponents (state source target certificate parameter : OTerm alpha)
    (h : Nonempty (Derivation body Delta (Fields state source target certificate parameter))) :
    ∀ i : Fin 4, Nonempty (Derivation body Delta
      (programGraph (![stateSource,stateTarget,stateCertificate,stateParameter] i)
        (![source,target,certificate,parameter] i) (Fin.cons state Fin.elim0))) := by
  intro i
  exact Fin.cases (projectLeft h) (Fin.cases (projectLeft (projectRight h))
    (Fin.cases (projectLeft (projectRight (projectRight h)))
      (Fin.cases (projectRight (projectRight (projectRight h))) (fun k => Fin.elim0 k)))) i

theorem atLiveValue (p : Program 4) (out state source target certificate parameter : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph4 live state source target certificate parameter)))
    (hp : Nonempty (Derivation body Delta (graph4 p out source target certificate parameter))) :
    Nonempty (Derivation body Delta (graph1 (atState p) out state)) :=
  compositionValue p ![stateSource,stateTarget,stateCertificate,stateParameter]
    out (Fin.cons state Fin.elim0) ![source,target,certificate,parameter] hp
    (fieldsComponents state source target certificate parameter
      (liveFields state source target certificate parameter hl))

theorem atLiveRecover (p : Program 4) (out state source target certificate parameter : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph4 live state source target certificate parameter)))
    (hp : Nonempty (Derivation body Delta (graph1 (atState p) out state))) :
    Nonempty (Derivation body Delta (graph4 p out source target certificate parameter)) :=
  compositionRecover p ![stateSource,stateTarget,stateCertificate,stateParameter]
    out (Fin.cons state Fin.elim0) ![source,target,certificate,parameter] hp
    (fieldsComponents state source target certificate parameter
      (liveFields state source target certificate parameter hl))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildStateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildStateProof
