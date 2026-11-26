# Numbered window framing and binder transport: source-first supporting targets

Sources: paper16 `sections/ordinals.tex` and the existing actual symbolic
`Comparison`/opening/closing and numbered raw/primary/storage definitions,
all pinned in `NUMBERED-WINDOW-FRAME-FROZEN.json`. This is not a positive
simulation endpoint, an assumption packaged as a transport, a quotient
enumerator, or certification of the numerical accessibility proof.

| Exact supporting target | Source correspondence |
| --- | --- |
| ClosingInventories | Ordinals 12–31, 219–225: global names are the typed pair `(σ,x)`. Numeric closing changes only a matching free name into the bound index at the current depth; original binders increment depth, already-bound positions stay put. Exact root type, declaration-support list and head list remain identical. |
| ClosingLexicalAdmissibility | Ordinals 26–31: both lexical environments are allowed, including actual finite context extensions. `CloseCompatible` requires a bound slot at the currently closing depth and retention of every already typed slot. This is the no-shift captured-name operation matching `StructuralContext.close`, **not** shifted insertion into an arbitrary incompatible context. Abs/FAbs need the actual empty context extended by the chosen name's type; lifted subderivations use matching pushed contexts. No global-name freshness restricts arbitrary trace closure. |
| ClosingBetaCommutes | Ordinals 51–58, 223–225: literal singleton beta removal and capture-avoiding depth shifts. In a body under `cutoff` residual binders the closing variable lies at `outer+cutoff+1` before removing the beta binder and at `outer+cutoff` afterward. Reinserted argument closes at its own original `outer` depth and is shifted only by the unchanged actual substitution algorithm. |
| ClosingRaw and ClosingPrimary | Ordinals 32–76: the original raw term witness (including the original Stat occurrence certificates, fixed declaration guards, and function-only closure) maps to the same raw relation. The equivalence witness remains typed, with original labels/head guards and genuine permitted base permutations. Beta and FAbs need factual commutation with raw substitution and fresh raw opening in the proof, not an assumed naturality field. |
| ClosingTypedTrace | Ordinals 219–225, 259–275: lift the actual mixed trace under a binder. It must retain literally the pointwise closed image of **every** original vertex, and exactly the original count of raw edges. Equivalence cannot contribute to positivity. No trace is supplied by definition; the input is the actual recursively known trace and the transformed trace is the conclusion. |
| ClosingRealization | Ordinals 228–232: closing is the same typed free-name map on symbolic and numerical shapes and preserves every actual finite label. The symbolic endpoint is the real `StructuralContext.close`, not a replacement symbolic constructor. |
| ClosingRecoversAbsBody | Ordinals 271; original `Tree.abs` / `Comparison.Weak.abs`: the same fresh typed name opens the actual original body by the real singleton binder removal. Close this actual opened numerical realization and recover exactly its original body. Freshness and lexical typing come from the original symbolic body and are not demanded of arbitrary intermediate raw nodes. |
| ClosingRecoversFAbsBody | Ordinals 51, 204, 276; original `Tree.fabs` / `Comparison.Weak.fabs`: the actual named child appends the one fresh free name to the old extras. The same closing at depth zero recovers the actual `openNumbered` result, with original lower label, copied original declaration, and old ordered arguments. Original owner typing and whole-owner free-name nonoccurrence are the literal certificate's conditions. |
| EnlargingAdmissibility, EnlargingRaw, EnlargingPrimary, EnlargingTypedTrace | Ordinals 12–24, 195–225, 298–301: enlarging a type window by literal list inclusion keeps the same signature, lexical context, raw term syntax and original declaration assumptions. Reinterpret each actual witness without changing its literal vertex list or positive raw edge count. No signature extension, changed head order, or source-window escape theorem is asserted. |

Proof staging after independent target review/preflight: (1) syntax
inventory/shift/application and beta commutation; (2) context typing and
original realization/Abs/FAbs roundtrips; (3) raw and primary witness
transport including exact occurrence maps; (4) window inclusion and mixed
trace lifts with literal vertices. Genuine positive simulation still has
to build the recursively budgeted raw/equivalence trace for every original
six-sort certificate. This packet does not replace those premises,
especially the two Stat trees, or include the marked-target extension.
