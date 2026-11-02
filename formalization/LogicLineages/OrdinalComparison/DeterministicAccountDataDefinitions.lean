module
public import LogicLineages.OrdinalComparison.DeterministicCarrierDataDefinitions
public import LogicLineages.OrdinalComparison.UnitHeadEvaluationDefinitions
public import LogicLineages.OrdinalComparison.SourceAnnotationBuilderDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.DeterministicAccountData
open ScalarAnnotationData ScalarCarrierAccounting SourceFreeOccurrences

structure UnaryRecord (Γ : List Ty) where
  source : OriginalTerm Γ (Ty.curriedGround 1)
  vector : OrdinalVector Γ 1

def UnaryRecord.Assigned {Γ} (r : UnaryRecord Γ) : Prop :=
  AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy r.source = some r.vector

def UnaryRecord.NoGround {Γ} (r : UnaryRecord Γ) : Prop :=
  ∀ x : Variable Γ .ground, (⟨Ty.ground,x⟩ : PackedVariable Γ) ∉ freeOccurrences r.source

/-- Proof-only certification does not select any data. -/
def certify {Γ} (r : UnaryRecord Γ) (ha : r.Assigned) (hn : r.NoGround) : Carrier :=
  ⟨Γ,r.source,r.vector,ha,hn⟩

def Matches {Γ} (r : UnaryRecord Γ) (label : Carrier) : Prop :=
  ∃ (ha : r.Assigned) (hn : r.NoGround), label = certify r ha hn

def carrierRecord {k Γ} (op : Operator (Ty.curriedGround (k+1) :: Γ)) :
    UnaryRecord (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ) :=
  ⟨(DeterministicCarrierData.carrierData op).source,(DeterministicCarrierData.carrierData op).vector⟩

/-- Whole-free-first literal accounting. Every classifier is the evaluated
closed-positive syntax algorithm; no ordinal comparison oracle is consulted. -/
def accountData {k Γ} (d : Tree k (Ty.curriedGround (k+1) :: Γ) .here) :
    Option (List (UnaryRecord (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ)) × Nat) :=
  if ordinalHeadFree (erase d) then some ([],1) else
  match d with
  | .free _ => none
  | .tracked => some ([],1)
  | .add a b => do
      let (xs,c) ← accountData a
      let (ys,e) ← accountData b
      pure (xs ++ ys,c+e+1)
  | .collapse op tail => do
      let a ← UnitHeadEvaluation.extractUnitHead op.head
      let (xs,c) ← accountData tail
      let code := ForwardTranslation.closedPositiveCode a
      if UnitHeadEvaluation.finiteCode code then
        pure (xs,c+UnitHeadEvaluation.finiteValueCode code+HeadFiniteSurplus.surplus op.head)
      else pure (xs ++ [carrierRecord op],c+HeadFiniteSurplus.surplus op.head)

/-- Original-source composition is ordinary Option bind, never extraction
of witnesses from a Prop theorem. -/
def sourceAccount {k Γ n}
    (e : TrackedSource.Expr k (Ty.curriedGround (k+1) :: Γ) .here n) := do
  let (u,d) ← SourceAnnotationBuilder.build e
  let (rs,c) ← accountData d
  pure (u,rs,c)
end LogicLineages.OrdinalComparison.Source.DeterministicAccountData
