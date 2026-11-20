import LogicLineages.PersistentMarking.NumberedWindowConstructorHeadProfileTargets
import LogicLineages.PersistentMarking.NumberedWindowConstructorOrderTargets

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorComputabilityTargets
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowArithmeticLeastClass NumberedWindowRules
open NumberedWindowConstructorArgumentAddresses NumberedWindowConstructorOrderTargets

inductive Owner where
  | ordinary (f : Head) (bs : NArgs)
  | numbered (f : Head) (τ : Ty) (k : Nat) (bs es : NArgs)

namespace Owner
def term : Owner → NTerm
  | .ordinary f bs => .ordinary f bs
  | .numbered f τ k bs es => .numbered f τ k bs es
def head : Owner → Head
  | .ordinary f _ | .numbered f _ _ _ _ => f
def base : Owner → NArgs
  | .ordinary _ bs | .numbered _ _ _ bs _ => bs
def label : Owner → Option Nat
  | .ordinary .. => none
  | .numbered _ _ k _ _ => some k
def extras : Owner → NArgs
  | .ordinary .. => .nil
  | .numbered _ _ _ _ es => es
def measure (o : Owner) (baseCodes extraCodes : List Nat) : Measure :=
  ⟨o.head,baseCodes,o.label,extraCodes⟩
end Owner

abbrev Members (S : Spine.Signature) (K Γ : List Ty) (hk : DecisionSourceUniverse.Closed K)
    (xs : NArgs) := ∀ q ∈ xs.toList, ComputableArgument S K Γ hk q

def Hypothesis (S : Spine.Signature) (K Γ : List Ty) (hk : DecisionSourceUniverse.Closed K)
    (m : Measure) : Prop :=
  ∀ (o : Owner) bs es, Slots S K Γ o.base bs → Slots S K Γ o.extras es →
    Earlier S K (o.measure bs es) m →
    InWindow S K (finiteC Γ) o.term.type o.term → Members S K Γ hk o.base → Members S K Γ hk o.extras →
    ComputableArgument S K Γ hk o.term

def RawCases (S : Spine.Signature) (K Γ : List Ty) (hk : DecisionSourceUniverse.Closed K) : Prop :=
  ∀ (o : Owner) bs es, Slots S K Γ o.base bs → Slots S K Γ o.extras es →
    InWindow S K (finiteC Γ) o.term.type o.term → Members S K Γ hk o.base → Members S K Γ hk o.extras →
    Hypothesis S K Γ hk (o.measure bs es) →
    ∀ r, RawStep S K o.term r → InWindow S K (finiteC Γ) o.term.type r → ComputableArgument S K Γ hk r

def OwnerComputability (S : Spine.Signature) (K Γ : List Ty) (hk : DecisionSourceUniverse.Closed K) : Prop :=
  ∀ o : Owner, InWindow S K (finiteC Γ) o.term.type o.term →
    Members S K Γ hk o.base → Members S K Γ hk o.extras → ComputableArgument S K Γ hk o.term

def ConstructorInductionFromRawCases : Prop :=
  ∀ S K Γ (hk : DecisionSourceUniverse.Closed K), RawCases S K Γ hk → OwnerComputability S K Γ hk

def AllConstructorRawCases : Prop :=
  ∀ S K Γ (hk : DecisionSourceUniverse.Closed K), RawCases S K Γ hk

def AllConstructorsComputable : Prop :=
  ∀ S K Γ (hk : DecisionSourceUniverse.Closed K), OwnerComputability S K Γ hk

end LogicLineages.PersistentMarking.NumberedWindowConstructorComputabilityTargets
