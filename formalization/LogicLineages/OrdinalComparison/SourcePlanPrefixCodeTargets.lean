module
public import LogicLineages.OrdinalComparison.SourcePlanPrefixCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePlanPrefixCode.Targets
open ExistentialPlan

def ActualEmbedding : Prop := ∀ (Γ : List Ty) (q : Plan Γ),
  (compile q).context.length=Γ.length+q.witnesses ∧
  ∀ (τ : Ty) (x : Variable Γ τ),
    SourceTypedPorts.variableIndex ((compile q).embedding x)=SourceTypedPorts.variableIndex x+q.witnesses

def ExactPrefixCalibration : Prop := ∀ (Γ Δ : List Ty) (k : Nat) (r : Renaming Γ Δ),
  (∀ (τ : Ty) (x : Variable Γ τ),SourceTypedPorts.variableIndex (r x)=SourceTypedPorts.variableIndex x+k) →
  (∀ (τ : Ty) (t : OriginalTerm Γ τ),
    ContextInsertionCode.sourceCode 0 k (SyntaxCode.encodeTerm t)=SyntaxCode.encodeTerm (t.rename r)) ∧
  (∀ es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground),
    shiftPairs k (es.map SourceGammaAggregateCode.pairCode)=
      (es.map (fun p => (p.1.rename r,p.2.rename r))).map SourceGammaAggregateCode.pairCode)

def UniformPrimitiveRecursive : Prop :=
  Primrec (fun p : Nat×(Nat×Nat) => shiftPair p.1 p.2) ∧ Primrec₂ shiftPairs
end LogicLineages.OrdinalComparison.Source.SourcePlanPrefixCode.Targets
