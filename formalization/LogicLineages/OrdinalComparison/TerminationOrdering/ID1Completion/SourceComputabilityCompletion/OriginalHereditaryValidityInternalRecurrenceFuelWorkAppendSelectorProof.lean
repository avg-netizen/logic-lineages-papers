module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalNodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendSelectorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- A derived proof schema, not an assumption on any source relation.
The selector's graph output is unchanged when the original raw and its own
parameter agree, independently of the remaining work suffix. -/
def SharedSelector (p : Program 1) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (state other raw parameter out : OTerm alpha),
  Nonempty (Derivation body Delta (graph1 currentRaw raw state)) →
  Nonempty (Derivation body Delta (graph1 currentRaw raw other)) →
  Nonempty (Derivation body Delta (graph1 currentParameter parameter state)) →
  Nonempty (Derivation body Delta (graph1 currentParameter parameter other)) →
  Nonempty (Derivation body Delta (graph1 p out state)) →
  Nonempty (Derivation body Delta (graph1 p out other))

 theorem rawShared : SharedSelector currentRaw := by
  intro body alpha Delta state other raw parameter out hr hother _ _ hp
  obtain ⟨he⟩ := valueUnique currentRaw out raw (Fin.cons state Fin.elim0) hp hr
  exact outputTransport currentRaw raw out (Fin.cons other Fin.elim0) ⟨symm he⟩ hother

 theorem parameterShared : SharedSelector currentParameter := by
  intro body alpha Delta state other raw parameter out _ _ hp hother hq
  obtain ⟨he⟩ := valueUnique currentParameter out parameter (Fin.cons state Fin.elim0) hq hp
  exact outputTransport currentParameter parameter out (Fin.cons other Fin.elim0) ⟨symm he⟩ hother

 theorem compositionShared {n : Nat} (f : Program n) (qs : Fin n → Program 1)
    (hq : ∀ i, SharedSelector (qs i)) : SharedSelector (.composition f qs) := by
  intro body alpha Delta state other raw parameter out hr hrOther hp hpOther ho
  apply programCompositionCases f qs out (Fin.cons state Fin.elim0) _ ho
  intro beta j ys Theta hj hv hqs
  rw [graph1Rename]
  simp only [consTermRename,emptyRename] at hqs
  have hr' := renameInto hr j Theta hj
  have hrOther' := renameInto hrOther j Theta hj
  have hp' := renameInto hp j Theta hj
  have hpOther' := renameInto hpOther j Theta hj
  rw [graph1Rename] at hr' hrOther' hp' hpOther'
  apply compositionValue f qs (out.relabel j) (Fin.cons (other.relabel j) Fin.elim0) ys hv
  intro i
  exact hq i body beta Theta (state.relabel j) (other.relabel j) (raw.relabel j)
    (parameter.relabel j) (ys i) hr' hrOther' hp' hpOther' (hqs i)

 theorem unaryShared (f p : Program 1) (hp : SharedSelector p) :
    SharedSelector (.composition f (fun _ : Fin 1 => p)) :=
  compositionShared f (fun _ : Fin 1 => p) (fun _ => hp)

 theorem binaryShared (f : Program 2) (p q : Program 1)
    (hp : SharedSelector p) (hq : SharedSelector q) : SharedSelector (.composition f ![p,q]) := by
  apply compositionShared f ![p,q]
  intro i
  exact Fin.cases hp (Fin.cases hq (fun j => Fin.elim0 j)) i

 theorem typeShared : SharedSelector currentType := unaryShared InternalUnpair.left currentRaw rawShared
 theorem domainShared : SharedSelector currentDomain := unaryShared OriginalLambdaConstructor.domain currentRaw rawShared
 theorem tagShared : SharedSelector currentTag := unaryShared OriginalLambdaConstructor.tag currentRaw rawShared

 theorem functionPayloadShared : SharedSelector (InternalApplicationStepPeel.functionPayload currentRaw) :=
  unaryShared InternalUnpair.left _
    (unaryShared InternalUnpair.right _
      (unaryShared InternalUnpair.right _ (unaryShared InternalUnpair.right _ rawShared)))

 theorem argumentPayloadShared : SharedSelector (InternalApplicationStepPeel.argumentPayload currentRaw) :=
  unaryShared InternalUnpair.right _
    (unaryShared InternalUnpair.right _
      (unaryShared InternalUnpair.right _ (unaryShared InternalUnpair.right _ rawShared)))

 theorem functionShared : SharedSelector currentFunction :=
  binaryShared InternalPairing.pairing _ _
    (binaryShared InternalListCodec.consCode _ _ domainShared typeShared) functionPayloadShared

 theorem argumentShared : SharedSelector currentArgument :=
  binaryShared InternalPairing.pairing _ _ domainShared argumentPayloadShared

 theorem codomainShared : SharedSelector currentCodomain :=
  unaryShared InternalListCodec.tailCode _ typeShared

 theorem bodyShared : SharedSelector currentBody :=
  binaryShared OriginalLambdaConstructor.bodyCode _ _ codomainShared rawShared

 theorem childParameterShared : SharedSelector childParameter :=
  binaryShared InternalPairing.pairing _ _
    (unaryShared InternalUnpair.left _ parameterShared)
    (binaryShared InternalListCodec.consCode _ _ domainShared
      (unaryShared InternalUnpair.right _ parameterShared))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendSelectorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendSelectorProof
