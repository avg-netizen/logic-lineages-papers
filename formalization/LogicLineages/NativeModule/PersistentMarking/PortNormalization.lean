module

public import LogicLineages.NativeModule.PersistentMarking.PortComparison
public import LogicLineages.NativeModule.PersistentMarking.DecisionSourceUniverse
public import LogicLineages.NativeModule.PersistentMarking.RefinementRenamingTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.PortNormalization
open Spine NameBridge DecisionInventory DecisionPorts DecisionObservations DecisionSourceUniverse RefinementRenamingTargets

structure Inputs (S : Signature) where
  source : Expr
  target : Expr
  sourceType : Ty
  targetType : Ty
  sourcePaper : PaperTerm S source sourceType
  targetPaper : PaperTerm S target targetType
  sourceOrdinary : Ordinary source
  targetOrdinary : Ordinary target

def Inputs.data (F : Inputs S) : InputInventory := inventory F.source F.target
def Source (F : Inputs S) (Γ : Context) (q : Expr) : Prop :=
  Universe F.data.types F.data.names F.data.sourceHeads Γ q
def Sources (F : Inputs S) (Γ : Context) (qs : Args) : Prop :=
  ArgsUniverse F.data.types F.data.names F.data.sourceHeads Γ qs
def Observed (F : Inputs S) (Γ : Context) (q : Expr) : Prop :=
  q ∈ observations F.data.names F.data.ports Γ F.target q.type
def ObservedArgs (F : Inputs S) (Γ : Context) (qs : Args) : Prop :=
  ∀ i q, At qs i q → Observed F Γ q

def OwnerSource (F : Inputs S) (Γ : Context) (f : Head) (bs es : Args) : Prop :=
  ∀ τ, τ ∈ F.data.types → Source F Γ (.marked f τ bs es)

/- The context and inventories are NOT silently renamed. Every induction
motive explicitly requires state/observation facts for the transformed terms. -/
def WeakMotive (F : Inputs S) (q t : Expr) : Prop := ∀ π Γ,
  injectiveNames π → WellFormed F.data.types F.data.ports Γ →
  Source F Γ (rename π q) → Observed F Γ (rename π t) →
  PortComparison.Weak S F.data.types F.data.names Γ (rename π q) (rename π t)
def StrictMotive (F : Inputs S) (q t : Expr) : Prop := ∀ π Γ,
  injectiveNames π → WellFormed F.data.types F.data.ports Γ →
  Source F Γ (rename π q) → Observed F Γ (rename π t) →
  PortComparison.Strict S F.data.types F.data.names Γ (rename π q) (rename π t)
def MatchingMotive (F : Inputs S) (qs ts : Args) : Prop := ∀ π Γ,
  injectiveNames π → WellFormed F.data.types F.data.ports Γ →
  Sources F Γ (renameArgs π qs) → ObservedArgs F Γ (renameArgs π ts) →
  PortComparison.Matching S F.data.types F.data.names Γ (renameArgs π qs) (renameArgs π ts)
def MultisetMotive (F : Inputs S) (qs ts : Args) : Prop := ∀ π Γ,
  injectiveNames π → WellFormed F.data.types F.data.ports Γ →
  Sources F Γ (renameArgs π qs) → ObservedArgs F Γ (renameArgs π ts) →
  PortComparison.Multiset S F.data.types F.data.names Γ (renameArgs π qs) (renameArgs π ts)
def CoverageMotive (F : Inputs S) (qs ts : Args) : Prop := ∀ π Γ,
  injectiveNames π → WellFormed F.data.types F.data.ports Γ →
  Sources F Γ (renameArgs π qs) → ObservedArgs F Γ (renameArgs π ts) →
  PortComparison.Coverage S F.data.types F.data.names Γ (renameArgs π qs) (renameArgs π ts)
def WholeMotive (F : Inputs S) (f : Head) (bs es ts : Args) : Prop := ∀ π Γ,
  injectiveNames π → WellFormed F.data.types F.data.ports Γ →
  OwnerSource F Γ f (renameArgs π bs) (renameArgs π es) → ObservedArgs F Γ (renameArgs π ts) →
  PortComparison.Whole S F.data.types F.data.names Γ f (renameArgs π bs) (renameArgs π es) (renameArgs π ts)
end LogicLineages.PersistentMarking.PortNormalization
