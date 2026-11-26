# Preserved failed native line attempt

Receipt `1794594817479263543-5`; formula native helpers passed, but lineEncoded
hit fixed 200000 heartbeats. Failed projection-reduction proof body:

```lean
 rcases line with ⟨context,raw,rule,payloadTag,payloadArgs,ref1,ref2⟩
 simp only [lineValidator,twoEval,lineContext,lineRaw,oneEval,
  HistoryDecoder.NativeProof.evaluateDecoder,encodeProd,encodeNat,Nat.unpair_pair]
 exact formulaEncoded context raw
```

The attempted singleton-vector proof also failed because get0/head were not
definitionally equal through Vector representation:

```lean
 have hv : v = v.head ::ᵥ nil := by
  ext i
  exact Fin.cases rfl (fun k => Fin.elim0 k) i
```

Repair splits actual line projections into small independent lemmas and uses
the established cons_head_tail/singleton_tail vector equations. No resource
limit or frozen specification changes.
