module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.NativeAtomsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.NativeFormulaProof
open GorbowPRProgram List.Vector HistoryRuleSuffix.NativeProof NativeAtomsProof
attribute [local irreducible] evaluate
theorem token0 (n : Nat) : evaluate formulaBranch (Nat.pair 1 n ::ᵥ 0 ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.expand (1,n) 0) := by
 simp [formulaBranch,whenEqualEval,projectionEval,get2_1,constantEval,oneAt,twoAt,binderAt,GorbowSyntaxValidation.expand]
theorem token1 (n : Nat) : evaluate formulaBranch (Nat.pair 1 n ::ᵥ 1 ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.expand (1,n) 1) := by
 simp [formulaBranch,whenEqualEval,projectionEval,get2_1,constantEval,oneAt,twoAt,binderAt,GorbowSyntaxValidation.expand]
theorem token2 (n : Nat) : evaluate formulaBranch (Nat.pair 1 n ::ᵥ 2 ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.expand (1,n) 2) := by
 simp [formulaBranch,whenEqualEval,projectionEval,get2_1,constantEval,oneAt,twoAt,binderAt,GorbowSyntaxValidation.expand]
theorem token3 (n : Nat) : evaluate formulaBranch (Nat.pair 1 n ::ᵥ 3 ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.expand (1,n) 3) := by
 simp [formulaBranch,whenEqualEval,projectionEval,get2_1,constantEval,oneAt,twoAt,binderAt,GorbowSyntaxValidation.expand]
theorem token4 (n : Nat) : evaluate formulaBranch (Nat.pair 1 n ::ᵥ 4 ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.expand (1,n) 4) := by
 simp [formulaBranch,whenEqualEval,projectionEval,get2_1,constantEval,oneAt,twoAt,binderAt,GorbowSyntaxValidation.expand]
theorem token5 (n : Nat) : evaluate formulaBranch (Nat.pair 1 n ::ᵥ 5 ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.expand (1,n) 5) := by
 simp [formulaBranch,whenEqualEval,projectionEval,get2_1,constantEval,oneAt,twoAt,binderAt,GorbowSyntaxValidation.expand]
theorem token6 (n : Nat) : evaluate formulaBranch (Nat.pair 1 n ::ᵥ 6 ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.expand (1,n) 6) := by
 simp [formulaBranch,whenEqualEval,projectionEval,get2_1,constantEval,oneAt,twoAt,binderAt,GorbowSyntaxValidation.expand]
theorem token7 (n : Nat) : evaluate formulaBranch (Nat.pair 1 n ::ᵥ 7 ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.expand (1,n) 7) := by
 simp [formulaBranch,whenEqualEval,projectionEval,get2_1,constantEval,oneAt,twoAt,binderAt,GorbowSyntaxValidation.expand]
theorem token8 (n : Nat) : evaluate formulaBranch (Nat.pair 1 n ::ᵥ 8 ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.expand (1,n) 8) := by
 simp [formulaBranch,whenEqualEval,projectionEval,get2_1,constantEval,oneAt,twoAt,binderAt,GorbowSyntaxValidation.expand]
theorem token9 (n : Nat) : evaluate formulaBranch (Nat.pair 1 n ::ᵥ 9 ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.expand (1,n) 9) := by
 simp [formulaBranch,whenEqualEval,projectionEval,get2_1,constantEval,oneAt,twoAt,binderAt,GorbowSyntaxValidation.expand]
theorem token10 (n : Nat) : evaluate formulaBranch (Nat.pair 1 n ::ᵥ 10 ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.expand (1,n) 10) := by
 simp [formulaBranch,whenEqualEval,projectionEval,get2_1,constantEval,oneAt,twoAt,binderAt,GorbowSyntaxValidation.expand]
theorem token11 (n : Nat) : evaluate formulaBranch (Nat.pair 1 n ::ᵥ 11 ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.expand (1,n) 11) := by
 simp [formulaBranch,whenEqualEval,projectionEval,get2_1,constantEval,oneAt,twoAt,binderAt,GorbowSyntaxValidation.expand]
theorem other (n token : Nat) (h : 12 ≤ token) : evaluate formulaBranch (Nat.pair 1 n ::ᵥ token ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.expand (1,n) token) := by
 have h0 : token ≠ 0 := by omega
 have h1 : token ≠ 1 := by omega
 have h2 : token ≠ 2 := by omega
 have h3 : token ≠ 3 := by omega
 have h4 : token ≠ 4 := by omega
 have h5 : token ≠ 5 := by omega
 have h6 : token ≠ 6 := by omega
 have h7 : token ≠ 7 := by omega
 have h8 : token ≠ 8 := by omega
 have h9 : token ≠ 9 := by omega
 have h10 : token ≠ 10 := by omega
 have h11 : token ≠ 11 := by omega
 simp [formulaBranch,whenEqualEval,projectionEval,get2_1,constantEval,GorbowSyntaxValidation.expand,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]
theorem branchAt (n token : Nat) : evaluate formulaBranch (Nat.pair 1 n ::ᵥ token ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.expand (1,n) token) := by
 by_cases h0 : token=0
 · subst token; exact token0 n
 by_cases h1 : token=1
 · subst token; exact token1 n
 by_cases h2 : token=2
 · subst token; exact token2 n
 by_cases h3 : token=3
 · subst token; exact token3 n
 by_cases h4 : token=4
 · subst token; exact token4 n
 by_cases h5 : token=5
 · subst token; exact token5 n
 by_cases h6 : token=6
 · subst token; exact token6 n
 by_cases h7 : token=7
 · subst token; exact token7 n
 by_cases h8 : token=8
 · subst token; exact token8 n
 by_cases h9 : token=9
 · subst token; exact token9 n
 by_cases h10 : token=10
 · subst token; exact token10 n
 by_cases h11 : token=11
 · subst token; exact token11 n
 exact other n token (by omega)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.NativeFormulaProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.NativeFormulaProof
