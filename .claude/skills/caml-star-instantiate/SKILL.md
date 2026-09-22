---
name: caml-star-instantiate
description: >-
  Add `instantiate!` proof-hint annotations to a Caml* (`.cst`) source file so its
  lemmas verify, using the "instantiated terms" ledger that `camlstar` prints for each
  counterexample. Use this whenever a Caml* / caml-star lemma fails to verify (the
  solver prints `[counterexample]`), when the user asks to add, infer, or synthesize
  `instantiate!` hints / instantiation annotations, to close spurious counterexamples
  that come from the relational abstraction, or to make a specific `tests/prop*.cst`
  (e.g. prop77) verify. This skill ONLY adds `instantiate!` annotations — it must not
  change any other part of the program (datatypes, function bodies, lemma statements).
---

# Adding `instantiate!` hints to Caml* from the ledger

## What this skill does — and its one hard rule

Caml* verifies pure, dependently-typed functional programs by discharging verification
conditions (VCs) with Z3. When a VC comes back `sat`, the solver reports a
`[counterexample]`. Often that counterexample is **spurious** — an artifact of the
*relational abstraction* (background below), not a real bug — and the fix is to add
`instantiate!(e)` hints that materialize the ground terms the solver is missing.

This skill does that **mechanically**, from a ledger the tool prints, not by squinting at
Z3 models. The method is a *frontier* search: take each applied term the query already
has, unfold its definition one step, and add whatever the unfolding produces that is not
already present. Repeat until the file verifies or the frontier proves a lemma is needed.

> **Hard rule: only add `instantiate!(…)` annotations (inside `let _ = instantiate!(…) in …`).
> Never modify anything else** — not the datatypes, not the function definitions, not the
> lemma statements, not the proof structure (matches/recursion). If a lemma cannot be
> closed by instantiations alone, say so and stop; do not "fix" it by editing code.

## Background: why instantiations are needed (read once)

Caml* does **not** hand a datatype function to Z3 as a function. It **relationally
abstracts** it: a user function or constructor `f : A → B` becomes a *relation*
`f_rel(args, result)` with a **functionality** axiom (same args ⇒ same result) and
**definitional equations** from `f`'s body. This keeps queries decidable (EPR), but it is
deliberately *incomplete* in one way: **totality is not asserted.** Nothing says every
application `f(args)` has a result, nor that every element of a datatype sort is reachable
by constructors. So a model may contain **"junk" elements** — an element of sort `nat`
that is neither `Z` nor `S` of anything.

A definitional equation like `max (S a') (S b') = S (max a' b')` is *guarded by the
constructor shape of its arguments*, and its right-hand side can only fire once the
witness `S (max a' b')` **exists** in the model. If that successor term is never
materialized, the equation stays silent and `max (S a') (S b')` is free to land on a junk
element — a spurious counterexample.

Caml* auto-materializes the applied subterms that **appear syntactically in the VC** (the
goal, the hypotheses, each recursive call). What it cannot invent are the
**constructor-of-a-recursive-subresult** witnesses that appear only *after* you unfold a
definition one step. `instantiate!(e)` supplies exactly those: it forces `e`'s applied
subterms to be materialized (an ∃-witness per call), so the guarded equations fire.

`instantiate!(e)` is **sound** (it only asserts witnesses that exist for total functions)
and **completeness-only**: adding one can turn a spurious `counterexample` into
`verified`, and it can never make a true `verified` become false. When in doubt, adding a
hint is safe — so the method below adds candidates in a batch, then trims.

## The ledger: your mechanical input

For every counterexample, `--solve` prints an **`instantiated terms:`** block right after
the model, and the same block appears as a `; instantiated terms:` comment atop each
query dumped with `--dump-smt`. It lists the user-function/constructor applications the
query has *in hand*, grouped by source:

```
instantiated terms:
  from the goal:            <- applications in the (negated) goal
    ...
  from the hypotheses:      <- recursive calls, guard predicates, constructor discriminators
    ...
  from the instantiate! hints:   <- what your current hints already added
    ...
```

This ledger **is** the set of ground terms the equations can currently fire on. Choosing
hints is then a diff: *find an application the proof needs to unfold, compute its one-step
result, and if that result is not in the ledger, add it.*

## The method (frontier search over the ledger)

Run everything from the `ocaml/` directory:

```
cd ocaml && eval "$(opam env)"
dune exec ./main.exe -- --solve tests/<FILE>.cst
```

There is one VC — hence potentially one counterexample — **per branch** of a lemma's
proof, so a lemma with several match arms yields several ledgers. Treat each independently.

For each counterexample:

**1. Identify the stuck term.** It is the goal's outermost application (e.g.
`max (max a b) c` or `sorted (insort x xs)`) — the equation whose value the model got
wrong. It is always in the `from the goal` group.

**2. Read the arm's constructor shapes from `from the hypotheses`.** The discriminators
there tell you which constructor each scrutinee took in this branch (`S a'`, `S b'` ⇒
`a = S a'`, `b = S b'`; a `Cons h t` with no deeper `Cons` ⇒ the tail is `Nil`). This is
the shape you unfold against — no need to decode the Z3 model.

**3. Build the frontier table.** Seed it with the stuck term and the goal's other
applications. For each row, fill:

| application | scrutinee shape (from hyps) | one-step result(s) | absent from ledger? |

- **one-step result(s):** open the function's definition in the source, take the arm
  matching the scrutinee shape, and read off the RHS. If that arm is `let p = g … in if p
  then A else B`, it has **two** results `A` and `B` (one per guard outcome) **and** the
  guard call `g …` is itself a term the model needs — list all three.
- **absent?** compare each result/guard term against **every** ledger group. Terms already
  present are *resolved* (skip them). Terms not present are **candidates**.

**4. Coverage pre-check (is this even an instantiation problem?).** A candidate is only
materializable if you can *write it from variables in scope in this arm* — i.e. its
subterms are built from the pattern binders and calls that appear in the ledger's goal or
hypotheses groups. If the term the proof needs mentions a value the arm never has (only an
*inductive hypothesis* would supply it), no ground witness exists — **stop and report that
a lemma is needed** (see Stop conditions). The tell-tale: unfolding the stuck term
reproduces a same-shaped application on strictly smaller arguments, and no base term ever
lands in the ledger to close the chain (unbounded induction, e.g. `∀n. eq_nat n n`).

**5. Batch-add every candidate, then re-run.** Add one `let _ = instantiate!(cand) in …`
per candidate, all at once, in the arm the counterexample belongs to. Re-solve. The new
witnesses appear under `from the instantiate! hints` in the next ledger and become
resolved; a candidate's own result may open a fresh frontier row (a deeper unfolding), so
this is a loop. Adding hints in a batch (rather than one at a time) collapses that loop.

**6. Minimize.** Once the file reports `N verified, 0 counterexamples`, remove hints one at
a time and re-run; drop any whose removal still verifies. This yields a minimal, readable
set (many arms need only a single hint — see below).

### Stop conditions

- **Verified.** All VCs pass after minimizing → done.
- **Lemma required.** The coverage pre-check fails / the frontier saturates: unfolding
  keeps producing structurally-similar applications on ever-smaller arguments and never
  bottoms out into a term already in the ledger. A finite set of ground instantiations
  cannot cover an unbounded inductive chain. **Report this; do not edit code.** (Example:
  `tip_04` needs `∀n. eq_nat n n`, a reflexivity lemma — no instantiation can supply it.)

## Where and how to write it

`instantiate!(e)` is a unit-valued expression; sequence it before the rest of the arm with
a wildcard let. `e` is any well-typed Caml* expression over the variables in scope
(constructor apps, function apps, nested); multiple hints stack:

```
| Z -> let _ = instantiate!(S (max a' b')) in ()
```
```
| Cons h2 t2 ->
    let _ = instantiate!(Cons x (Cons h2 t2)) in
    let _ = instantiate!(Cons h2 (insort x t2)) in
    tip_77 x t
```

## Worked example — prop22 (`max` associativity)

`tests/prop22.cst` proves `max (max a b) c = max a (max b c)` by induction on `a, b, c`.
Unannotated, `--solve` gives **3 verified, 1 counterexample**, on the base arm
`a = S a', b = S b', c = Z`. Its ledger:

```
instantiated terms:
  from the goal:
    max a b
    max (max a b) c
    max b c
    max a (max b c)
  from the hypotheses:
    S a'
    S b'
  from the instantiate! hints:
    (none)
```

Run the frontier method:

1. **Stuck term:** `max (max a b) c`.
2. **Shapes (from hyps):** `a = S a'`, `b = S b'`; and `c = Z` (this is the `c = Z` arm).
3. **Frontier:**

   | application | shape | one-step result | absent? |
   |---|---|---|---|
   | `max a b` = `max (S a') (S b')` | both `S` | `S (max a' b')` | **yes** ← candidate |
   | `max b c` = `max (S b') Z` | `S`, `Z` | `S b'` | no (in hyps) |
   | `max (max a b) c` | needs `max a b` first | `S (max a' b')` | same candidate |
   | `max a (max b c)` = `max (S a') (S b')` | both `S` | `S (max a' b')` | same candidate |

   The whole goal reduces to the single missing witness `S (max a' b')`. Note `a'`, `b'`
   appear nowhere else in this arm (no recursive call), which is *why* auto-materialization
   never built it.
4. **Coverage:** `S (max a' b')` is writable from the in-scope binders `a'`, `b'` — this is
   an instantiation problem, not a lemma.
5. **Add & re-run:**
   ```
   | Z -> let _ = instantiate!(S (max a' b')) in ()
   ```
   → **4 verified, 0 counterexamples.** The recursive arm `c = S c'` needs nothing: its
   `tip_22 a' b' c'` call already materializes the successors (they show up under
   `from the hypotheses` in that arm's ledger).

**prop31 (`min`)** is structurally identical: the same `c = Z` arm, the same single
candidate `S (min a' b')`, closed by `| Z -> let _ = instantiate!(S (min a' b')) in ()`.
The lesson both teach: the witness is **constructor-of-the-recursive-call**, and the
ledger tells you it is absent.

## Generalizing to lists and Bool predicates (e.g. prop77)

`tests/prop77.cst` proves `sorted xs ==> sorted (insort x xs)`. Here the stuck goal term is
a **`Bool` predicate** application, `sorted (insort x xs)`, and `insort` builds its result
out of **`Cons`** — but only after an internal `le` guard. The `t = Nil` arm's ledger:

```
  from the goal:
    sorted xs
    insort x xs
    sorted (insort x xs)
  from the hypotheses:
    Cons h t
    le x h
    le h x
    le_neg x h
  from the instantiate! hints:
```

Frontier: pin `insort x xs` = `insort x (Cons h t)`. Its `Cons h t` arm is
`let p = le x h in if p then Cons x (Cons h t) else Cons h (insort x t)` — **two** results,
`Cons x (Cons h t)` and `Cons h (insort x t)`, plus the guard `le x h` (already in hyps).
Neither `Cons` term is in the ledger → both are candidates. Once they exist, `sorted`'s
equations can finally unfold on `insort x xs`. In the deeper `t = Cons h2 t2` arm, the
recursive `tip_77 x t` already lists `insort x t` in its ledger, so there the candidates
are the *next* layer — `Cons x (Cons h2 t2)` and `Cons h2 (insort x t2)`. Batch-add per
arm, re-run, and minimize.

The principle is unchanged from `nat`: **an application stuck at a junk value ⇒ materialize
what it unfolds to one step.** Only the constructor changes (`S` → `Cons`), a `Bool`
predicate like `sorted` is pinned indirectly by materializing the constructor terms it
inspects, and a function with an internal guard contributes **one candidate per branch**.

## Sanity checks

- After each edit, `dune build` stays clean and the counterexample count goes **down** (or
  a new, deeper counterexample appears — that is progress). If a hint changes the ledger by
  nothing, you named a term that was already present — re-read the frontier row.
- A hint may only use variables **in scope** in its arm (the coverage pre-check).
- If, after materializing every one-step frontier candidate, a counterexample persists and
  the frontier only reproduces smaller same-shaped applications (no closing base term),
  the obligation needs an **inductive lemma**, not an instantiation. Report it; don't edit.
