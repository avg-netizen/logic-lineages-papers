module

public import LogicLineages.PersistentMarking.NumberedWindowScalarAlgorithm
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticLexicalTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowAdmissionTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticClassAlgorithmTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticExchangeTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticAllContextBits

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarTargets
open Spine NumberedWindowScalarAlgorithm NumberedWindowArithmeticTyCode NumberedWindowArithmeticTermCode
open NumberedWindowTypingBits NumberedWindowArithmeticLeastClass NumberedWindowArithmeticAllContextBits

def fixed (S : Signature) (K : List Ty) : Settings :=
  ⟨NumberedWindowAdmissionTargets.window S K,K.map encodeTy,NumberedWindowArithmeticExchangeAtomsTargets.pairs S K⟩

def ExactGuardedExchange : Prop := ∀ S K Γ τ,
  (∀ n, admitted (fixed S K) (Γ.map encodeTy) (encodeTy τ) n =
    (decodeTerm n).any (finiteWindowBit S K Γ τ)) ∧
  (∀ a b, edge (fixed S K) (Γ.map encodeTy) (encodeTy τ) a b =
    NumberedWindowArithmeticClassAlgorithmTargets.codedExchange S K Γ τ a b)

def ExactLeastRepresentative : Prop := ∀ S K Γ τ n,
  least (fixed S K) (Γ.map encodeTy) (encodeTy τ) n = (decodeTerm n).bind (leastCode S K Γ τ)

def ExactScalarAddress : Prop := ∀ S K, scalar (fixed S K) = addressBit S K
end LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarTargets
