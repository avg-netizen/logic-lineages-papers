module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ParameterTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.AnswersProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerGuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ChildInputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z)
open InputProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def childInputs (xs : Fin 6 → OTerm alpha) (child childBound : OTerm alpha) : Fin 6 → OTerm alpha :=
  ![child,childBound,xs 2,xs 3,xs 4,xs 5]

theorem parameterAt (xs : Fin 6 → OTerm alpha) (child childBound param : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs))) :
    Nonempty (Derivation body Delta (programGraph parameterQuery param (childInputs xs child childBound))) :=
  ParameterTransportProof.transport xs (childInputs xs child childBound) param rfl rfl rfl rfl hp

theorem toExtract (n : Nat) (xs : Fin 6 → OTerm alpha) (child childBound childKey param value : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childKey child childBound)))
    (hf : Nonempty (Derivation body Delta (programGraph (fields n) value (childInputs xs child childBound)))) :
    Nonempty (Derivation body Delta (graph2 (extract n) value childKey param)) :=
  extractFromFields n (childInputs xs child childBound) childKey param value
    (keyValue (childInputs xs child childBound) childKey hk) (parameterAt xs child childBound param hp) hf

theorem fromExtract (n : Nat) (xs : Fin 6 → OTerm alpha) (child childBound childKey param value : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childKey child childBound)))
    (hf : Nonempty (Derivation body Delta (graph2 (extract n) value childKey param))) :
    Nonempty (Derivation body Delta (programGraph (fields n) value (childInputs xs child childBound))) :=
  fieldsFromExtract n (childInputs xs child childBound) childKey param value
    (keyValue (childInputs xs child childBound) childKey hk) (parameterAt xs child childBound param hp) hf

theorem singletonAnswers (n : Nat) (key param childKey deps value values : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps childKey z)))
    (hv : Nonempty (Derivation body Delta (graph2 (extract n) value childKey param)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values value z))) :
    Nonempty (Derivation body Delta (graph2 (Equation.answers n) values key param)) :=
  AnswersProof.answersAt n key param deps values hd
    (AnswersProof.consMap n deps childKey z z param value values hc (AnswersProof.nilMap n param) hv hl)

theorem firstValue (key param values value tail : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values value tail))) :
    Nonempty (Derivation body Delta (graph3 firstAnswer value key values param)) := by
  obtain ⟨h⟩ := InternalListCodecSupportProof.consDestruction values value tail hl
  have hh := Nonempty.intro (Derivation.conjunctionLeft h)
  exact LayerGuardProof.unaryVectorValue InternalListCodec.headCode (.projection 1) value values ![key,values,param]
    hh (projectionValue 1 ![key,values,param])
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ChildInputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ChildInputProof
