import LogicLineages.PersistentMarking.NativeRSContextProof
namespace LogicLineages.PersistentMarking.NativeRSChainsProof
open Spine NativeReduction NativeTypingProof NativeRSFamiliesProof NativeRSContextProof

theorem toStep (S : Signature) (τ : Ty) (n A B : Expr)
    (hn : PaperTerm S n .ground) (hA : PaperTerm S A (stepType τ)) (hoA : Ordinary A) (hB : PaperTerm S B τ) :
    Weak S (C0 τ n A B (stepType τ)) A := by
  have hf := familyTyping S τ n A B hn hA hB
  have h2 : Weak S (C2 τ n A B (stepType τ)) A :=
    secondSelect S (stepType τ) (.arrow τ τ) _ A (.cons (P τ n A B τ) .nil)
      (rec1Paper S τ (succ n) (succPaper S n hn)) hA hoA (.cons (hf.p τ).1 .nil) ⟨(hf.p τ).2,True.intro⟩
  have h1 : Weak S (C1 τ n A B (stepType τ)) A :=
    .select (domains := []) (hf.c1 (stepType τ)) hA (Or.inr .here) (hf.c2 (stepType τ)).1 rfl h2
  exact .select (domains := []) (hf.c0 (stepType τ)) hA (Or.inr (.there .here)) (hf.c1 (stepType τ)).1 rfl h1

theorem toNumber (S : Signature) (τ : Ty) (n A B : Expr)
    (hn : PaperTerm S n .ground) (hon : Ordinary n) (hA : PaperTerm S A (stepType τ)) (hB : PaperTerm S B τ) :
    Weak S (C0 τ n A B .ground) n := by
  have hf := familyTyping S τ n A B hn hA hB
  have hw := ElementaryProof.strictIncluded S (succ n) n (succStrict S n hn hon).2.1
  have h1 : Weak S (C1 τ n A B .ground) n :=
    .select (domains := []) (hf.c1 .ground) hn (Or.inl (.there .here)) (succPaper S n hn).1 rfl hw
  exact .select (domains := []) (hf.c0 .ground) hn (Or.inr .here) (hf.c1 .ground).1 rfl h1

theorem toRecursion (S : Signature) (τ : Ty) (n A B : Expr)
    (hn : PaperTerm S n .ground) (hon : Ordinary n) (hA : PaperTerm S A (stepType τ)) (hoA : Ordinary A)
    (hB : PaperTerm S B τ) (hoB : Ordinary B) :
    Weak S (C0 τ n A B τ) (recTerm τ n A B) := by
  have hf := familyTyping S τ n A B hn hA hB
  have ht := recPaper S τ n A B hn hA hB
  have h2 : Weak S (C2 τ n A B τ) (recTerm τ n A B) :=
    .select (domains := []) (hf.c2 τ) ht (Or.inr .here) (hf.p τ).1 rfl
      (predecessorWeak S τ n A B hn hon hA hoA hB hoB)
  have h1 : Weak S (C1 τ n A B τ) (recTerm τ n A B) :=
    .select (domains := []) (hf.c1 τ) ht (Or.inr (.there .here)) (hf.c2 τ).1 rfl h2
  exact .select (domains := []) (hf.c0 τ) ht (Or.inr (.there (.there .here))) (hf.c1 τ).1 rfl h1
end LogicLineages.PersistentMarking.NativeRSChainsProof
