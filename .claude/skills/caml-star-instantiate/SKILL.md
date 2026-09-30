---
name: caml-star-instantiate
description: >-
  Add `instantiate!` proof-hint annotations to a Caml* (`.cst`) source file so its
  lemmas verify, by reading the counterexample `camlstar --solve` prints and unfolding the
  stuck application one step in the source. Use this whenever a Caml* / caml-star lemma
  fails to verify (the solver reports a failed VC with a counterexample), when the user asks to add, infer,
  or synthesize `instantiate!` hints / instantiation annotations, to close spurious
  counterexamples that come from the relational abstraction, or to make a specific
  `prop*.cst` (e.g. prop77) verify. This skill ONLY adds `instantiate!` annotations —
  it must not change any other part of the program (datatypes, function bodies, lemma
  statements).
---

# Adding `instantiate!` hints to Caml* from the counterexample

## What this skill does — and its one hard rule

Caml* discharges verification conditions (VCs) with Z3. When a VC comes back `sat`, the
solver prints it as `[VC#i: failed] <reason>` with its counterexample model and an
`• Instantiated terms:` list. Often the counterexample is **spurious** — an artifact of the
*relational abstraction* (described in the Background section below), not a real bug — and 
the fix is to add `instantiate!(e)` hints that materialize the ground terms the solver is missing.

The method is a **hybrid**. The **source definition** supplies the one-step unfolding of each
application; the **instantiated-terms list** says whether that unfolding is already present —
if it is absent, the equation could not have fired and the application is **stuck**; and the
**counterexample** confirms the branch and shows which wrong value the solver chose. The hint
`e` in `instantiate!(e)` is a valid source term, never a decoded model element.

> **Hard rule: only add `instantiate!(…)` annotations (inside `let _ = instantiate!(…) in …`).
> Never modify anything else** — not the datatypes, not the function definitions, not the
> lemma statements, not the proof structure (matches/recursion). If a lemma cannot be closed
> by instantiations alone, report SATURATED (below); do not "fix" it by editing code.

> **This is the instantiation stage of `caml-star-prove`** (the top-level Caml\* proof
> skill), which owns the full background and the handoff to lemmas. Invoked directly, this
> skill stands alone and finishes with the report contract below.

## Background: why instantiations are needed

Caml\* generates verification conditions in (pure) first-order logic and hands them over
to Z3. However, functions in the VC are not encoded as functions; they are 
**relationally abstracted**: a user function or constructor `f : A → B` becomes a relation 
`f_rel(args, result)` with a **functionality** axiom (same args ⇒ same result) and a set of
**definitional equations** obtained from the function body. For constructors, **injectivity** 
(`f(x) = f(y) => x = y`) is asserted in addition. This keeps queries decidable (EPR) 
but is deliberately *incomplete* because **totality** of functions is never asserted: nothing 
says every application `f(args)` has a result, nor that every element of a datatype sort is 
reachable by constructors. In other words, all functions are **partial**, meaning that `f(args)`
may be undefined for some `args`. This makes it possible for Z3 to return spurious models that 
seemingly violate definitional equations because the corresponding relationally
abstracted axioms are vacuously satisfied. For example, consider the following
definitional equation of `max` defined on an inductive `nat` datatype:

```
max (S a') (S b') = S (max a' b')
```

The corresponding relationally abstracted axiom is:

```
∀(a b a' b' t0 t1 : nat), S_rel(a',a) ∧ S_rel(b',b) 
               ∧ max_rel(a', b', t0) ∧ S_rel(t0, t1) => max_rel(a,b,t1)
```

Observe that the axiom can be vacuously satified by falsifying any of the relation applications
in the antecedent. This allows the solver to build spurious models where `max (S a') (S b')` is 
unrelated to `max a' b'`. We say that the above definitional equation for `max` "did not fire" 
and `max (S a') (S b')` is "stuck". The equation can only fire once the witness `S (max a' b')` 
is materialized in the VC. Caml* auto-materializes the applied subterms that appear 
syntactically in the VC (goal, hypotheses, recursive calls), but the terms that appear only after 
unfolding one or two steps are what it misses. These terms need to be explicitly instantiated using 
Caml*'s `instantiate!` keyword. Adding `instantiate!(e)` forces `e`'s applied subterms into the VC, 
allowing the guarded equations to fire. Instantiation is always **sound** --- adding an instantiation will 
only ever eliminate a *spurious* counterexample; never a real counterexample --- and 
**eventually complete** --- if the original VC (sans relational abstraction) is UNSAT, then adding 
enough instantiations will eventually make the relational VC UNSAT.

## Reading Caml*'s output

Each failing VC prints as `[VC#i: failed] <reason>` followed by four labelled parts:

- **`• Location:` `<file>:<sl>:<sc>-<el>:<ec>`** — the source span of the obligation (the lemma
  definition). In a large file, open exactly that region.
- **`• Hypotheses:`** — the facts in scope in this branch: the match **discriminators**
  (`a = (S a')`, `b = (S b')`, `c = Z`), the **recursive/lemma calls**, and any **guards**.
  This gives the arm's full constructor shapes directly — including nullary ones like `c = Z`
  that never appear as an application — so you do not need `--print-vcs` for them.
- **`• Counterexample:`** — the model, printed JSON-*like* but **quote-free** (keys and values
  are bare), with three parts:
  - **sort universes** — the finite element set of each datatype: `nat: [nat!6, nat!5, nat!0,
    Z]`;
  - **program-variable assignments** — `a: nat!1`, including the arm's pattern binders
    (`a': nat!0`);
  - **function maps** — each user function/constructor as a table whose entries use `↦`, with
    a tuple on the left for several arguments:
    `S: { nat!0 ↦ nat!1 }`, `max: { (nat!1, nat!3) ↦ nat!6, … }`.
- **`• Instantiated terms:`** (below).

**Stuck.** An application `f(args)` is **stuck** when its value **disagrees with `f`'s
definition** unfolded one step on the args' constructor shapes — the equation never fired. Two
ways to see it, and the first is usually quicker: the one-step unfolding
`C (f subargs)` is **absent** from the `• Instantiated terms:` list (so the equation *could
not* have fired), or the model's value for `f(args)` simply differs from that unfolding's.

The `• Instantiated terms:` list (also a `; instantiated terms:` comment atop each `--dump-smt`
query) is the flat set of applications the query already materialises as witnesses. You use it
to **test stuckness** (is the one-step unfolding present?), to **dedup** (don't re-add a term
already present), and for **saturation** (below). It tells you *whether* a witness is missing;
the model and the source tell you *which* application to unfold and *what* the witness is.

## The method

Run from `ocaml/`, where `<target>.cst` is the file you are annotating (a path relative to
`ocaml/`, or an absolute one):

```
cd ocaml && eval "$(opam env)"
dune exec ./main.exe -- --solve <target>.cst
```

One VC per proof branch, so a lemma with several arms yields several counterexamples; treat
each independently. For each failed VC:

**0. Do a saturation pre-check** to ensure that adding instantiations can indeed work. See
the section on Stop Conditions for instructions on how to check for saturation.

**1. Locate the stuck application.** Walk the goal's applications. For each, take its args'
constructor shapes (from `• Hypotheses:`) and ask whether every term (i.e., a function 
application) resulting from its one-step unfolding is **present** in the `• Instantiated terms:` 
list; if it is absent, that equation could not have fired and the application is **stuck**. 
Prefer the **innermost** stuck application: an outer one is often stuck only because an 
argument is (e.g. `max (max a b) c` is stuck because `max a b` is) — fixing the inner one is 
what matters. Handle all independently-stuck applications.

**2. Confirm.** For each term `f(args)` resulting from one-step unfolding, if it is absent in the
`• Instantiated terms:` list, check if the counterexample model assigns any value to `f(args)`. 
If the value is undefined (possible because `f` is encoded as a partial function in SMT), then we 
get the confirmation that `f(args)` is (most likely) the missing instantiation that preempts the 
current counterexample.

**3. Write the fix.** In the current proof arm, assert the existence of `f(args)` by adding
an instantiation annotation of the form `let _ = instantiate!(f(args)) in e`, where `e` is
the current expression in this proof arm. Several instantiations can be stacked by nesting the
`let` expressions. Since `args` are derived from hypotheses of the current arm, `f(args)` must 
be a well-formed expression. If not, then it isn't an instantiation — see SATURATED.

**4. Re-run & Verify** Re-run Caml* and verify that the previously failed VC now either passes
or generates a new counterexample. A new counterexample is possible because a newly instantiated
term may expose a deeper stuck application next round — this is a loop.

## Stop conditions and the report contract

Finish by reporting exactly one verdict, so a caller (`caml-star-prove`) can act on it:

- **DISCHARGED.** All VCs pass after adding instantiations → report the final 
  `N verified, 0 failed` and the hints kept. Done.
- **SATURATED.** Instantiation cannot close it — hand off to a lemma. Two tells:
  1. **No stuck application has constructor-shaped arguments**, yet the VC is still `sat`.
     Every remaining discrepancy is on an **opaque argument** — a bare variable, or an
     application whose own value is unknown — so there is no constructor shape to unfold
     against and no single witness to materialize. A free **Bool guard** on opaque args is the
     same story (e.g. `eq_nat n n` with `n` an opaque parameter). This needs case analysis or
     induction, i.e. a lemma.
  2. **Instantiations loop:** when a function `f` mentioned in the proof is defined recursively,
     but the recursion is non-structural or non-terminating, then unrolling `f` results in terms
     with ever-larger constructor arguments. We call this an *instantiation loop*. The tell-tale
     sign of an instantiation loop is the presence of several constructor applications of 
     increasing size in the `• Instantiated terms:` list, e.g., `S(a)`, `S(S(a))`, `S(S(S(a)))` 
     and so on. A finite set of instantiations cannot prove this goal; we need induction or
     a lemma.
  In either case, **report SATURATED; do not edit further.** List each still-red VC with its 
  stuck goal term and the un-closable application (the evidence a lemma is needed). Keep any hints 
  that were independently useful. (Example: `tip_04` needs `∀n. eq_nat n n`, a reflexivity lemma.)

When run as the instantiation gate of `caml-star-prove`, SATURATED hands control back to it
to hypothesize the lemma; run directly, SATURATED is the final answer (a lemma is out of this
skill's scope).

## Worked example — prop22 (`max` associativity)

`Examples/prop22.cst` (bundled with this skill, already annotated) proves
`max (max a b) c = max a (max b c)` by induction on `a, b, c`. Strip its hint and `--solve`
gives **3 verified, 1 failed** on the base arm:

```
...
[VC#3: failed] definition of tip_22
• Location: Examples/prop22.cst:14:0-20:51
• Hypotheses:
    a = (S a')
    b = (S b')
    c = Z
• Counterexample:
    nat: [nat!6, nat!5, nat!2, nat!1, nat!0, nat!3, Z],
    a: nat!1,  b: nat!3,  c: Z,  a': nat!0,  b': nat!2,
    S: { nat!2 ↦ nat!3, nat!0 ↦ nat!1 },
    max: { (nat!1, nat!3) ↦ nat!6, (nat!6, Z) ↦ nat!5, (nat!3, Z) ↦ nat!3,
           (Z, nat!6) ↦ nat!6, (Z, nat!5) ↦ nat!5, 
           (Z, nat!2) ↦ nat!2, (Z, nat!1) ↦ nat!1, (Z, nat!0) ↦ nat!0, 
           (Z, nat!3) ↦ nat!3, (Z, Z) ↦ Z}
• Instantiated terms:
    max a b, max (max a b) c, max b c, max a (max b c), S a', S b'
...
```

1. **Locate.** The printed `• Location: Examples/prop22.cst:14:0-20:51` corresponds to 
   the inductive proof of `tip_22` lemma, which asserts `max (max a b) c = max a (max b c)`.
   Given the `• Hypotheses`, i.e., `a = S a'`, `b = S b'`, & `c = Z`, `max a b` in the goal
   should unfold to `S (max a' b')`, which should make it possible to apply the inductive 
   hypothesis (IH) and prove the goal. However, under relational abstraction, where 
   functions are partial, this bridge between IH and the goal breaks down since the 
   term `S (max a' b')` may not be defined: `max` may be undefined on inputs `a' b'`, or `S` 
   may be undefined on `max a' b'`. 

2. **Confirm** Indeed, the term `S (max a' b')` is **absent** from 
   the `• Instantiated terms:` list, so the definitional equation of `max` relating
   `max (S x') (S y')` to `max x' y'` could not fire. The `• Counterexample` model confirms 
   it: `max a' b'` = `max nat!0 nat!2` is undefined. We say `max a b` is **stuck** since its 
   definitional axiom could not fire. Note that `max (max a b) c = max nat!6 Z` is stuck too, but
   only *transitively*: `nat!6` is not constrained to any constructor shape, so no definitional
   axiom for the outer `max` can match its first argument either. The **innermost** stuck
   application is `max a b`, so we will focus on that.
3. **Write the fix.** `max a b` can be unstuck by asserting the existence of the term `S (max a' b')`.
   The term is well-formed in the current arm of the proof since `a'` and `b'` are in scope. We
   assert its existence by adding `instantiate!(S (max a' b'))`:
   ```
   | Z -> let _ = instantiate!(S (max a' b')) in ()
   ```
4. **Re-run & Verify** Running Caml* on the annotated proof discharges the goal: the result is
   **4 verified, 0 failed.** The recursive arm `c = S c'` needs nothing — its `tip_22 a' b' c'` 
   call already materializes the successors.

## Worked example — prop77 (lists and a guarded body)

`Examples/prop77.cst` (bundled, already annotated) proves `sorted xs ==> sorted (insort x xs)`.
Strip both its hints and you'll see two failures: one for the `xs = Cons h t && t = Nil` arm, 
and the other for the `xs = Cons h t && t = Cons h2 t2` arm. Let us focus on the first failure. Caml* 
generates the following failure output: 

```
[VC#5: failed] definition of tip_77
• Location: Examples/prop77.cst:35:0-43:18
• Hypotheses:
    xs = (Cons h t)
    ((~(le x h)) ==> (le h x)) /\ (u1 = (le_neg x h))
    t = Nil
• Counterexample:
    natlist: [natlist!2, Nil, natlist!1],
    nat: [Z, nat!1, nat!0],
    x: nat!1,  xs: natlist!1,  h: nat!0,  t: Nil,
    le:     {(Z, Z) ↦ true, (Z, nat!1) ↦ true, (Z, nat!0) ↦ true,
             (nat!1, Z) ↦ false, (nat!1, nat!1) ↦ false, (nat!1, nat!0) ↦ false,
             (nat!0, Z) ↦ false, (nat!0, nat!1) ↦ true, (nat!0, nat!0) ↦ false},
    Cons:   { (nat!0, Nil) ↦ natlist!1, (nat!0, natlist!2) ↦ natlist!2 },
    insort: { (nat!1, natlist!1) ↦ natlist!2 },
    sorted: { natlist!1 ↦ true, natlist!2 ↦ false, Nil ↦ true }
• Instantiated terms:
    sorted xs
    insort x xs
    sorted (insort x xs)
    Cons h t
    le x h
    le h x
    le_neg x h
```

1. **Locate.** The printed `• Location: Examples/prop77.cst:35:0-43:18` corresponds to 
   the inductive proof of `tip_77` lemma, which asserts `sorted xs ==> sorted (insort x xs)`.
   Given the `• Hypotheses`, i.e., `xs = (Cons h t)` & `t = Nil`,  the term `insort x xs` 
   in the goal should unfold to:
   ```
   let p = le x h in if p then Cons x (Cons h t) else Cons h (insort x t)
   ```
   In the "then" branch, `Cons h t` is already instantiated, and `Cons x (Cons h t)` term is 
   built when the corresponding `insort` axiom is applied. Since `t = Nil` and `le x h`, the 
   goal is easily discharged. In the "else" branch, given `t = Nil`, the term `Cons h (insort x t)` 
   should reduce to `Cons h (Cons x Nil)`, which should be easily provable since `~(le x h)`. 
   However, under relational abstraction, the term `insort x t` (therefore `Cons h (insort x t)`) 
   may not exist, which allows `insort x xs` to return an arbitrary list that is not `sorted`. 

2. **Confirm** Indeed, the term `insort x t` is **absent** from 
   the `• Instantiated terms:` list, so the definitional axiom of `insort x xs` corresponding to
   `xs = Cons h t` could not fire. The `• Counterexample` model confirms 
   it: `insort x t` = `insort nat!1 Nil` is undefined. `insort x xs` is therefore **stuck** when 
   `xs = Cons h t` and `t = Nil`.

3. **Write the fix.** `insort x xs` can be made unstuck by instantiating `Cons h (insort x t)`, 
   which also instantiates `insort x t`, and makes it possible for the definitional axiom of `insort` 
   to fire. The term is well-formed in the current arm of the proof since `h`, `x` and `t` are all
   in scope. The fix is therefore to add the following annotation to the proof arm 
   corresponding to `xs = Cons h t` & `t = Nil`:
   ```
   let _ = instantiate!(Cons h (insort x t)) in ()
   ```
4. **Re-run & Verify** Running Caml* on the annotated proof now makes VC#5 verified. We could have 
   done similar reasoning in the proof arm corresponding to `xs = Cons h t` & `t = Cons h2 t2`, 
   and it would have led us to the following annotation in this branch:
   ```
   let _ = instantiate!(Cons h2 (insort x t2)) in tip_77 x t
   ```
   Assuming both annotations are added, Caml* would discharge the proof: 
   **6 verified, 0 failed**. 


## When it is NOT an instantiation — prop04

In `Examples/prop04.cst`, the `tip_04` obligation `S (count n xs) = count n (Cons n xs)` has 
**no stuck application with constructor-shaped arguments**: the discrepancy is the guard `eq_nat(n, n)`, 
which the model sets to `false` inside `count n (Cons n xs)`, firing the wrong branch. But `n` is the 
opaque lemma parameter — no constructor shape, so `eq_nat`'s equations can't unfold and there is no 
witness to materialize. This is SATURATED tell #1. Report it; `caml-star-prove` supplies the lemma
`∀x. eq_nat x x`.

## Sanity checks

- After each edit, `dune build` stays clean and the failed-VC count goes **down** (or a new,
  deeper counterexample appears — that is progress). If a hint changes nothing, you unfolded
  the wrong (already-materialized) application — re-read which value is stuck.
- A hint may only use variables **in scope** in its arm.
- No stuck application has constructor-shaped arguments but the VC is still `sat`, or the
  instantiations loop → SATURATED: report that a lemma is needed; don't edit.
